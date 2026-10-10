import OAI.Analysis.AncientFlat.Evolution.FamilyCancellation

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction SchwartzMap
namespace SourceFrozenCancellation
open SchwartzTimeScale
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
def timeDiff (K : SchwartzMap V E) (N : ℕ) (ell a : ℝ) (z : V) : E :=
  atTime K N (ell*a) z-atTime K N a z
lemma scaled_mem {α β ell a : ℝ} (hα : 0<α) (hell : ell∈Icc (1:ℝ) 2) (ha : a∈Icc α β) :
    ell*a∈Icc α (2*β) := by
  have hap : 0<a := hα.trans_le ha.1
  constructor
  · exact ha.1.trans (le_mul_of_one_le_left hap.le hell.1)
  · exact mul_le_mul hell.2 ha.2 hap.le (by norm_num)
lemma timeDiff_continuous (K : SchwartzMap V E) (N : ℕ) {α β ell : ℝ}
    (hα : 0<α) (hell : ell∈Icc (1:ℝ) 2) (a : V → ℝ) (ha : Continuous a)
    (har : ∀ z, a z∈Icc α β) : Continuous (fun z => timeDiff K N ell (a z) z) := by
  exact (continuous_variable K N (fun z => ell*a z) (continuous_const.mul ha)
    (fun z => mul_pos (zero_lt_one.trans_le hell.1) (hα.trans_le (har z).1))).sub
    (continuous_variable K N a ha (fun z => hα.trans_le (har z).1))
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma integral_timeDiff_zero (K : SchwartzMap V E) (N : ℕ) (hz : ∫ z,K z=0)
    {ell a : ℝ} (hell : 0<ell) (ha : 0<a) : ∫ z,timeDiff K N ell a z=0 := by
  have hi (q : ℝ) (hq : 0<q) : Integrable (fun z => atTime K N q z) := by
    obtain ⟨B,hB,_,_,hb⟩ := parameter_envelope K N q q hq
    exact hB.mono' (continuous_variable K N (fun _ => q) continuous_const (fun _ => hq)).aestronglyMeasurable
      (Eventually.of_forall (hb q ⟨le_rfl,le_rfl⟩))
  unfold timeDiff
  rw [integral_sub (hi _ (mul_pos hell ha)) (hi _ ha),integral_atTime_zero K N _ (mul_pos hell ha) hz,
    integral_atTime_zero K N a ha hz,sub_self]
lemma timeDiff_envelopes (K : SchwartzMap V E) (N : ℕ) (α β : ℝ)
    (hα : 0<α) (hαβ : α≤β) :
    ∃ B C : V → ℝ, Integrable B ∧ Integrable (fun z => (1+‖z‖)*B z) ∧
      (∀ z, 0≤B z) ∧ Integrable C ∧ Integrable (fun z => (1+‖z‖)*C z) ∧
      (∀ z, 0≤C z) ∧ ∀ ell∈Icc (1:ℝ) 2,
      (∀ a∈Icc α β, ∀ z, ‖timeDiff K N ell a z‖≤(ell-1)*B z) ∧
      (∀ a∈Icc α β, ∀ b∈Icc α β, ∀ z,
        ‖timeDiff K N ell a z-timeDiff K N ell b z‖≤((ell-1)*C z)*‖a-b‖) := by
  have hβ : 0<β := hα.trans_le hαβ
  obtain ⟨D,hD,hDw,hDp,hd⟩ := parameter_lipschitz_envelope K N α (2*β) hα
  obtain ⟨P,hP,hPw,hPp,hp⟩ := parameter_envelope (euler K N) (N+4) α (2*β) hα
  obtain ⟨Q,hQ,hQw,hQp,hq⟩ := parameter_lipschitz_envelope (euler K N) (N+4) α (2*β) hα
  let B := fun z => β*D z
  let C := fun z => P z+β*Q z
  have hBi : Integrable B := hD.const_mul β
  have hBw : Integrable (fun z => (1+‖z‖)*B z) := by
    simpa only [B,mul_left_comm,mul_assoc] using hDw.const_mul β
  have hCi : Integrable C := hP.add (hQ.const_mul β)
  have hCw : Integrable (fun z => (1+‖z‖)*C z) := by
    convert hPw.add (hQw.const_mul β) using 1
    ext z; dsimp [C]; ring
  refine ⟨B,C,hBi,hBw,fun z => mul_nonneg hβ.le (hDp z),hCi,hCw,
    fun z => add_nonneg (hPp z) (mul_nonneg hβ.le (hQp z)),?_⟩
  intro ell hell
  have hδ : 0≤ell-1 := sub_nonneg.mpr hell.1
  have hmem {a : ℝ} (ha : a∈Icc α β) : a∈Icc α (2*β) := ⟨ha.1,by linarith [ha.2]⟩
  have hdist {a : ℝ} (ha : a∈Icc α β) : ‖ell*a-a‖≤β*(ell-1) := by
    rw [Real.norm_eq_abs,show ell*a-a=(ell-1)*a by ring,abs_of_nonneg (mul_nonneg hδ (hα.le.trans ha.1))]
    nlinarith [mul_le_mul_of_nonneg_left ha.2 hδ]
  constructor
  · intro a ha z
    exact (hd _ (scaled_mem hα hell ha) _ (hmem ha) z).trans
      ((mul_le_mul_of_nonneg_left (hdist ha) (hDp z)).trans_eq (by dsimp [B]; ring))
  · intro a ha b hb z
    have hder (q : ℝ) (hr : q∈Icc α β) :
        HasDerivAt (fun q => timeDiff K N ell q z)
          (ell • atTime (euler K N) (N+4) (ell*q) z-atTime (euler K N) (N+4) q z) q := by
      have h := ((hasDerivAt_atTime K N (ell*q)
        (mul_pos (zero_lt_one.trans_le hell.1) (hα.trans_le hr.1)) z).scomp q
          ((hasDerivAt_id q).const_mul ell)).sub (hasDerivAt_atTime K N q (hα.trans_le hr.1) z)
      convert h using 1 <;> try rfl
      simp only [mul_one]
    have hbd (q : ℝ) (hr : q∈Icc α β) :
        ‖ell • atTime (euler K N) (N+4) (ell*q) z-atTime (euler K N) (N+4) q z‖≤(ell-1)*C z := by
      let e1 := atTime (euler K N) (N+4) (ell*q) z
      let e0 := atTime (euler K N) (N+4) q z
      have he : ell • e1-e0=(ell-1) • e1+(e1-e0) := by module
      change ‖ell • e1-e0‖≤_
      rw [he]
      calc
        _ ≤ ‖(ell-1) • e1‖+‖e1-e0‖ := norm_add_le ..
        _ ≤ (ell-1)*P z+Q z*(β*(ell-1)) := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hδ]
          exact add_le_add (mul_le_mul_of_nonneg_left (hp _ (scaled_mem hα hell hr) z) hδ)
            ((hq _ (scaled_mem hα hell hr) _ (hmem hr) z).trans
              (mul_le_mul_of_nonneg_left (hdist hr) (hQp z)))
        _ = _ := by dsimp [C]; ring
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun q hq => (hder q hq).hasDerivWithinAt) hbd (convex_Icc α β) hb ha
end SourceFrozenCancellation

end

end OAI
