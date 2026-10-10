import OAI.MathematicalPhysics.AlternatingFlow.DecayBounds

namespace OAI

section CertifiedBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter
namespace AlternatingNS.Effective

variable {A E F : Type*} [Primcodable A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def weight (z : ℝ × Space) : ℝ := 1 + |z.1| + ‖z.2‖

lemma weight_pos (z : ℝ × Space) : 0 < weight z := by unfold weight; positivity

def Certified (f : A → ℝ × Space → F) : Prop :=
  (∀ a, ContDiff ℝ ∞ (f a)) ∧ ∃ B : A × ℕ × ℕ → ℕ, Computable B ∧
    ∀ a J r z, weight z ^ J * ‖iteratedFDeriv ℝ r (f a) z‖ ≤ B (a,J,r)

lemma velocity_certified : Certified (fun z : Machine × List ℕ => Function.uncurry (Construction.velocity z.1 z.2)) := by
  obtain ⟨C,hC,hc⟩ := pulsePiece_decay
  let B := fun z : (Machine × List ℕ) × ℕ × ℕ =>
    11^z.2.1 * C (z.1,z.2.2) * (1 + 8 * 2^z.2.1 * z.2.1.factorial)
  have cb : Computable B := by
    have hJ : Computable (fun z : (Machine × List ℕ) × ℕ × ℕ => z.2.1) := Computable.fst.comp Computable.snd
    exact Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (nat_pow.to_comp.comp (Computable.const 11) hJ)
        (hC.comp (Computable.fst.pair (Computable.snd.comp Computable.snd))))
      (Primrec.nat_add.to_comp.comp (Computable.const 1)
        (Primrec.nat_mul.to_comp.comp
          (Primrec.nat_mul.to_comp.comp (Computable.const 8) (nat_pow.to_comp.comp (Computable.const 2) hJ))
          (factorial.to_comp.comp hJ)))
  refine ⟨fun z => Construction.velocity_smooth z.1 z.2, B, cb, ?_⟩
  rintro ⟨M,w⟩ J r z
  have hc' (n : ℕ) : weight z ^ J * ‖iteratedFDeriv ℝ r (Bounds.pulsePiece M w n) z‖ ≤
      11^J * (C ((M,w),r) : ℝ) * ((1+(n:ℝ))^J * Bounds.amplitude M w.length n) := by
    by_cases hz : z ∈ tsupport (iteratedFDeriv ℝ r (Bounds.pulsePiece M w n))
    · have hsupport := Bounds.pulsePiece_support M w n (tsupport_iteratedFDeriv_subset r hz)
      have ht : 0 ≤ z.1 := (Nat.cast_nonneg n).trans hsupport.1.1
      have hw : weight z ^ J ≤ (11 * (1+(n:ℝ)))^J := by
        apply pow_le_pow_left₀ (weight_pos z).le
        dsimp [weight]; rw [abs_of_nonneg ht]
        linarith [hsupport.1.2, Bounds.box_norm z.2 hsupport.2, Nat.cast_nonneg (α := ℝ) n]
      calc
        _ ≤ (11*(1+(n:ℝ)))^J * ((C ((M,w),r) : ℝ) * Bounds.amplitude M w.length n) :=
          mul_le_mul hw (hc M w r n z) (norm_nonneg _) (by positivity)
        _ = _ := by rw [mul_pow]; ring
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero, mul_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (Bounds.amplitude_nonneg M w.length n))
  obtain ⟨N,hN⟩ := TimeGlue.locally_eq_sum Profiles.pulse Profiles.pulse_zero_left (Construction.piece M w) z
  change Function.uncurry (Construction.velocity M w) =ᶠ[𝓝 z]
    (fun z => ∑ n ∈ Finset.range N, Bounds.pulsePiece M w n z) at hN
  rw [(hN.iteratedFDeriv ℝ r).eq_of_nhds,
    iteratedFDeriv_fun_sum_apply (fun n _ => (Bounds.pulsePiece_smooth M w n).of_le
      (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  have ha := Bounds.weighted_amplitude_summable M w.length J
  calc
    _ ≤ weight z ^ J * ∑ n ∈ Finset.range N, ‖iteratedFDeriv ℝ r (Bounds.pulsePiece M w n) z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (weight_pos z).le J)
    _ ≤ ∑ n ∈ Finset.range N, 11^J * (C ((M,w),r):ℝ) * ((1+(n:ℝ))^J * Bounds.amplitude M w.length n) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun n _ => hc' n)
    _ ≤ (11^J * (C ((M,w),r):ℝ)) * ∑' n : ℕ, (1+(n:ℝ))^J * Bounds.amplitude M w.length n := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (ha.sum_le_tsum _ (fun n _ => mul_nonneg (by positivity) (Bounds.amplitude_nonneg M w.length n))) (by positivity)
    _ ≤ B ((M,w),J,r) := by
      have h := mul_le_mul_of_nonneg_left (weighted_amplitude_sum M w.length J)
        (show (0:ℝ) ≤ 11^J * C ((M,w),r) by positivity)
      simpa only [B, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

lemma Certified.congr {f g : A → ℝ × Space → F} (hf : Certified f) (h : ∀ a z, f a z = g a z) : Certified g := by
  rwa [← funext (fun a => funext (h a))]

lemma Certified.param {B : Type*} [Primcodable B] {f : A → ℝ × Space → F}
    (hf : Certified f) (g : B → A) (hg : Computable g) : Certified (fun b => f (g b)) := by
  obtain ⟨hs,C,hC,h⟩ := hf
  exact ⟨fun b => hs (g b), fun z => C (g z.1,z.2), hC.comp ((hg.comp Computable.fst).pair Computable.snd), fun b => h (g b)⟩

lemma Certified.add {f g : A → ℝ × Space → F} (hf : Certified f) (hg : Certified g) :
    Certified (fun a z => f a z + g a z) := by
  obtain ⟨sf,B,hB,hf⟩ := hf
  obtain ⟨sg,C,hC,hg⟩ := hg
  refine ⟨fun a => (sf a).add (sg a), fun z => B z + C z,
    Primrec.nat_add.to_comp.comp hB hC, fun a J r z => ?_⟩
  rw [fun_iteratedFDeriv_add_apply ((sf a).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((sg a).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt, Nat.cast_add]
  calc
    _ ≤ weight z ^ J * (‖iteratedFDeriv ℝ r (f a) z‖ + ‖iteratedFDeriv ℝ r (g a) z‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg (weight_pos z).le _)
    _ ≤ _ := by rw [mul_add]; exact add_le_add (hf a J r z) (hg a J r z)

lemma Certified.linear {f : A → ℝ × Space → F} (hf : Certified f)
    (L : A → F →L[ℝ] E) (D : A → ℕ) (hD : Computable D) (hL : ∀ a, ‖L a‖ ≤ D a) :
    Certified (fun a => L a ∘ f a) := by
  obtain ⟨hs,B,hB,hf⟩ := hf
  refine ⟨fun a => (L a).contDiff.comp (hs a), fun z => D z.1 * B z,
    Primrec.nat_mul.to_comp.comp (hD.comp Computable.fst) hB, fun a J r z => ?_⟩
  calc
    _ ≤ weight z ^ J * ((D a : ℝ) * ‖iteratedFDeriv ℝ r (f a) z‖) :=
      mul_le_mul_of_nonneg_left ((Bounds.norm_postcomp_linear (f a) (hs a) (L a) r z).trans
        (mul_le_mul_of_nonneg_right (hL a) (norm_nonneg _))) (pow_nonneg (weight_pos z).le _)
    _ ≤ _ := by rw [mul_left_comm, Nat.cast_mul]; exact mul_le_mul_of_nonneg_left (hf a J r z) (Nat.cast_nonneg _)

lemma Certified.csmul {f : A → ℝ × Space → F} (hf : Certified f) (c : ℝ) (D : ℕ) (hc : |c| ≤ D) :
    Certified (fun a z => c • f a z) := by
  apply hf.linear (fun _ => c • ContinuousLinearMap.id ℝ F) (fun _ => D) (Computable.const D)
  intro _
  simpa only [norm_smul, Real.norm_eq_abs, mul_one] using
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := F)) (abs_nonneg c)).trans (by simpa using hc)

lemma Certified.sub {f g : A → ℝ × Space → F} (hf : Certified f) (hg : Certified g) :
    Certified (fun a z => f a z - g a z) := by
  exact (hf.add (hg.csmul (-1) 1 (by norm_num))).congr (by intros; simp [sub_eq_add_neg])

lemma Certified.directional {f : A → ℝ × Space → F} (hf : Certified f)
    (v : A → ℝ × Space) (hv : ∀ a, ‖v a‖ ≤ 1) :
    Certified (fun a z => fderiv ℝ (f a) z (v a)) := by
  obtain ⟨sf,B,hB,hf⟩ := hf
  refine ⟨fun a => ((sf a).fderiv_right (by simp)).clm_apply contDiff_const,
    fun z => B (z.1,z.2.1,z.2.2+1), hB.comp (Computable.fst.pair
      ((Computable.fst.comp Computable.snd).pair (Computable.succ.comp (Computable.snd.comp Computable.snd)))), fun a J r z => ?_⟩
  apply le_trans _ (hf a J (r+1) z)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (weight_pos z).le _)
  exact (Bounds.norm_directional_iterated (f a) (sf a) (v a) r z).trans
    (mul_le_of_le_one_left (norm_nonneg _) (hv a))

lemma Certified.smul {f : A → ℝ × Space → ℝ} {g : A → ℝ × Space → F}
    (hf : Certified f) (hg : Certified g) : Certified (fun a z => f a z • g a z) := by
  obtain ⟨sf,B,hB,hf⟩ := hf
  obtain ⟨sg,C,hC,hg⟩ := hg
  let D := fun z : A × ℕ × ℕ => ∑ i ∈ Finset.range (z.2.2+1), z.2.2.choose i * B (z.1,z.2.1,i) * C (z.1,0,z.2.2-i)
  have hi : Computable₂ (fun z : A × ℕ × ℕ => fun i : ℕ => z.2.2.choose i * B (z.1,z.2.1,i) * C (z.1,0,z.2.2-i)) := by
    have ha : Computable (fun z : (A × ℕ × ℕ) × ℕ => z.1.1) := Computable.fst.comp Computable.fst
    have hJ : Computable (fun z : (A × ℕ × ℕ) × ℕ => z.1.2.1) := Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hr : Computable (fun z : (A × ℕ × ℕ) × ℕ => z.1.2.2) := Computable.snd.comp (Computable.snd.comp Computable.fst)
    exact Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp
      (choose.to_comp.comp hr Computable.snd) (hB.comp (ha.pair (hJ.pair Computable.snd))))
      (hC.comp (ha.pair ((Computable.const 0).pair (Primrec.nat_sub.to_comp.comp hr Computable.snd))))
  refine ⟨fun a => (sf a).fun_smul (sg a), D,
    (nat_sum_range hi).comp Computable.id (Computable.succ.comp (Computable.snd.comp Computable.snd)), fun a J r z => ?_⟩
  apply (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le (sf a) (sg a) z
    (WithTop.coe_le_coe.mpr le_top)) (pow_nonneg (weight_pos z).le J)).trans
  simp only [D, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ = (r.choose i : ℝ) * (weight z^J * ‖iteratedFDeriv ℝ i (f a) z‖) * ‖iteratedFDeriv ℝ (r-i) (g a) z‖ := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hf a J i z) (Nat.cast_nonneg _))
      (by simpa using hg a 0 (r-i) z) (norm_nonneg _) (by positivity)

end AlternatingNS.Effective

end CertifiedBoundsDevelopment

end OAI
