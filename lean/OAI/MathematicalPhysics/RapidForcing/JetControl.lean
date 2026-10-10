import OAI.MathematicalPhysics.RapidForcing.QuantitativeDecay

namespace OAI

open scoped BigOperators Topology ENNReal ContDiff
open Set Filter
namespace RapidForcing

def JetControl {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Field E) (B : ℕ → ℕ → ℚ) : Prop :=
  ∃ g : ℝ × Space → E, ContDiff ℝ (⊤ : ℕ∞) g ∧
    (∀ t, 0 ≤ t → ∀ x, v t x = g (t,x)) ∧
    ∀ J k p, (1+‖p‖)^J * ‖iteratedFDeriv ℝ k g p‖ ≤ (B J k : ℝ)

namespace JetControl
section General
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {v w : Field E} {B C : ℕ → ℕ → ℚ}

lemma nonneg (hv : JetControl v B) (J k : ℕ) : 0 ≤ B J k := by
  obtain ⟨g, _, _, hb⟩ := hv
  have h := (mul_nonneg (by positivity : 0 ≤ (1+‖(0:ℝ × Space)‖)^J)
    (norm_nonneg _)).trans (hb J k 0)
  exact_mod_cast h

lemma add (hv : JetControl v B) (hw : JetControl w C) :
    JetControl (fun t x => v t x + w t x) (fun J k => B J k + C J k) := by
  obtain ⟨g,hg,he,hb⟩ := hv
  obtain ⟨h,hh,he',hc⟩ := hw
  refine ⟨fun p => g p+h p, hg.add hh, fun t ht x => by dsimp only; rw [he t ht x,he' t ht x], ?_⟩
  intro J k p
  rw [fun_iteratedFDeriv_add_apply (hg.of_le (finite_order k)).contDiffAt
    (hh.of_le (finite_order k)).contDiffAt, Rat.cast_add]
  calc
    _ ≤ (1+‖p‖)^J * (‖iteratedFDeriv ℝ k g p‖ + ‖iteratedFDeriv ℝ k h p‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ _ := by rw [mul_add]; exact add_le_add (hb J k p) (hc J k p)

lemma sub (hv : JetControl v B) (hw : JetControl w C) :
    JetControl (fun t x => v t x - w t x) (fun J k => B J k + C J k) := by
  obtain ⟨g,hg,he,hb⟩ := hv
  obtain ⟨h,hh,he',hc⟩ := hw
  refine ⟨fun p => g p-h p, hg.sub hh, fun t ht x => by dsimp only; rw [he t ht x,he' t ht x], ?_⟩
  intro J k p
  rw [fun_iteratedFDeriv_sub_apply (hg.of_le (finite_order k)).contDiffAt
    (hh.of_le (finite_order k)).contDiffAt, Rat.cast_add]
  calc
    _ ≤ (1+‖p‖)^J * (‖iteratedFDeriv ℝ k g p‖ + ‖iteratedFDeriv ℝ k h p‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ _ := by rw [mul_add]; exact add_le_add (hb J k p) (hc J k p)

lemma zero : JetControl (fun _ _ => (0:E)) (fun _ _ => 0) := by
  refine ⟨fun _ => 0, contDiff_const, by simp, ?_⟩
  intro J k p
  simp

lemma sum {ι : Type} (s : Finset ι) {f : ι → Field E} {D : ι → ℕ → ℕ → ℚ}
    (hf : ∀ i ∈ s, JetControl (f i) (D i)) :
    JetControl (fun t x => ∑ i ∈ s, f i t x) (fun J k => ∑ i ∈ s, D i J k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (E:=E))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma const_smul (hv : JetControl v B) (r : ℝ) (q : ℚ) (hq : ‖r‖ ≤ (q:ℝ)) :
    JetControl (fun t x => r • v t x) (fun J k => q * B J k) := by
  obtain ⟨g,hg,he,hb⟩ := hv
  refine ⟨fun p => r • g p, hg.const_smul r, fun t ht x => by dsimp only; rw [he t ht x], ?_⟩
  intro J k p
  rw [iteratedFDeriv_const_smul_apply' (hg.of_le (finite_order k)).contDiffAt,
    norm_smul, Rat.cast_mul]
  calc
    _ = ‖r‖ * ((1+‖p‖)^J * ‖iteratedFDeriv ℝ k g p‖) := by ring
    _ ≤ _ := mul_le_mul hq (hb J k p) (by positivity) ((norm_nonneg _).trans hq)

lemma postcomp (hv : JetControl v B) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) :
    JetControl (fun t x => L (v t x)) B := by
  obtain ⟨g,hg,he,hb⟩ := hv
  refine ⟨fun p => L (g p), L.contDiff.comp hg, fun t ht x => by dsimp only; rw [he t ht x], ?_⟩
  intro J k p
  exact (mul_le_mul_of_nonneg_left (by simpa using jet_postcomp_le L hg k p 1 hL)
    (by positivity)).trans (hb J k p)

lemma direction_bound {g : ℝ × Space → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v : ℝ × Space) (hv : ‖v‖ ≤ 1) (k : ℕ) (p : ℝ × Space) :
    ‖iteratedFDeriv ℝ k (fun q => fderiv ℝ g q v) p‖ ≤
      ‖iteratedFDeriv ℝ (k+1) g p‖ := by
  have h := norm_iteratedFDeriv_clm_apply_const (c := v) (x := p)
    (hg.fderiv_right (by simp)).contDiffAt (finite_order k)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h.trans (by
    simpa using mul_le_mul_of_nonneg_right hv (norm_nonneg (iteratedFDeriv ℝ (k+1) g p)))

lemma spatialD (hv : JetControl v B) (i : Fin 3) :
    JetControl (RapidForcing.spatialD i v) (fun J k => B J (k+1)) := by
  obtain ⟨g,hg,he,hb⟩ := hv
  refine ⟨fun p => fderiv ℝ g p (0,basis i),
    (hg.fderiv_right (by simp)).clm_apply contDiff_const, ?_, ?_⟩
  · intro t ht x
    have hd : HasFDerivAt (fun y : Space => g (t,y))
        ((fderiv ℝ g (t,x)).comp ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) x :=
      ((hg.differentiable (by simp) _).hasFDerivAt).comp x
        ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    change fderiv ℝ (v t) x (basis i) = _
    rw [show v t = fun y => g (t,y) from funext (he t ht), hd.fderiv]
    rfl
  · intro J k p
    exact (mul_le_mul_of_nonneg_left
      (direction_bound hg (0,basis i) (by simp [basis]) k p) (by positivity)).trans (hb J (k+1) p)

lemma timeD (hv : JetControl v B) :
    JetControl (RapidForcing.timeD v) (fun J k => B J (k+1)) := by
  obtain ⟨g,hg,he,hb⟩ := hv
  refine ⟨fun p => fderiv ℝ g p (1,0),
    (hg.fderiv_right (by simp)).clm_apply contDiff_const, ?_, ?_⟩
  · intro t ht x
    have hd : HasDerivAt (fun s : ℝ => g (s,x)) (fderiv ℝ g (t,x) (1,0)) t :=
      ((hg.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    change derivWithin (fun s => v s x) (Ici 0) t = _
    rw [derivWithin_congr (s := Ici (0:ℝ)) (fun s hs => he s hs x) (he t ht x),
      hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)]
  · intro J k p
    exact (mul_le_mul_of_nonneg_left
      (direction_bound hg (1,0) (by simp) k p) (by positivity)).trans (hb J (k+1) p)

lemma spatialD_iterate (hv : JetControl v B) (i : Fin 3) (n : ℕ) :
    JetControl ((RapidForcing.spatialD i)^[n] v) (fun J k => B J (k+n)) := by
  induction n with
  | zero => simpa using hv
  | succ n ih => simpa only [Function.iterate_succ_apply', Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using ih.spatialD i

lemma timeD_iterate (hv : JetControl v B) (n : ℕ) :
    JetControl (RapidForcing.timeD^[n] v) (fun J k => B J (k+n)) := by
  induction n with
  | zero => simpa using hv
  | succ n ih => simpa only [Function.iterate_succ_apply', Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using ih.timeD

lemma mixedD (hv : JetControl v B) (l : ℕ) (α : MultiIndex) :
    JetControl (RapidForcing.mixedD l α v) (fun J k => B J (k + (l+α 0+α 1+α 2))) := by
  simpa only [RapidForcing.mixedD, spatialMulti, Nat.add_assoc] using
    (((hv.spatialD_iterate 2 (α 2)).spatialD_iterate 1 (α 1)).spatialD_iterate 0 (α 0)).timeD_iterate l

lemma mixed_bound (hv : JetControl v B) (J l : ℕ) (α : MultiIndex) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    (1+t+‖x‖)^J * ‖RapidForcing.mixedD l α v t x‖ ≤
      ((2^J * B J (l+α 0+α 1+α 2) : ℚ) : ℝ) := by
  obtain ⟨g,hg,he,hb⟩ := hv.mixedD l α
  have ht' : t ≤ ‖(t,x)‖ := by simp [Real.norm_eq_abs, abs_of_nonneg ht]
  have hx' := norm_snd_le (t,x)
  have hw : 1+t+‖x‖ ≤ 2*(1+‖(t,x)‖) := by linarith
  have h := hb J 0 (t,x)
  simp only [norm_iteratedFDeriv_zero, Nat.zero_add] at h
  rw [he t ht x, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  calc
    _ ≤ (2*(1+‖(t,x)‖))^J * ‖g (t,x)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hw J) (norm_nonneg _)
    _ = (2:ℝ)^J * ((1+‖(t,x)‖)^J * ‖g (t,x)‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
end General

lemma smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Field ℝ} {w : Field E} {B C : ℕ → ℕ → ℚ}
    (hv : JetControl v B) (hw : JetControl w C) :
    JetControl (fun t x => v t x • w t x)
      (fun J k => 2^k * ∑ i ∈ Finset.range (k+1), B J i * C 0 (k-i)) := by
  have hBN := hv.nonneg
  have hCN := hw.nonneg
  obtain ⟨g,hg,he,hb⟩ := hv
  obtain ⟨h,hh,he',hc⟩ := hw
  refine ⟨fun p => g p • h p, hg.smul hh, fun t ht x => by dsimp only; rw [he t ht x, he' t ht x], ?_⟩
  intro J k p
  have hC (i : ℕ) : ‖iteratedFDeriv ℝ i h p‖ ≤ (C 0 i : ℝ) := by simpa using hc 0 i p
  calc
    _ ≤ (1+‖p‖)^J * ∑ i ∈ Finset.range (k+1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i g p‖ * ‖iteratedFDeriv ℝ (k-i) h p‖ :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hg hh p (finite_order k)) (by positivity)
    _ = ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
        ((1+‖p‖)^J * ‖iteratedFDeriv ℝ i g p‖) * ‖iteratedFDeriv ℝ (k-i) h p‖ := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ ∑ i ∈ Finset.range (k+1), (2:ℝ)^k * (B J i : ℝ) * (C 0 (k-i) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul _ (hC (k-i)) (norm_nonneg _) (by exact mul_nonneg (by positivity) (by exact_mod_cast hBN J i))
      exact mul_le_mul (by exact_mod_cast Nat.choose_le_two_pow k i) (hb J i p)
        (by positivity) (by positivity)
    _ = _ := by simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

end JetControl

def forceJetBound (d : ScaleData) (νBound : ℚ) (J k : ℕ) : ℚ :=
  velocityJetBound d J (k+1) +
    3*(2^k * ∑ i ∈ Finset.range (k+1), velocityJetBound d J i * velocityJetBound d 0 (k-i+1)) +
    νBound * (3 * velocityJetBound d J (k+1+1))

lemma addressedVelocity_jetControl (M : Machine) (w : M.Input) :
    JetControl (addressedVelocity M w) (velocityJetBound (M.scaleData w)) :=
  ⟨Function.uncurry (addressedVelocity M w), addressedVelocity_joint_smooth M w,
    fun _ _ _ => rfl, addressedVelocity_weighted_jetBound M w⟩

lemma addressedForce_jetControl (ν : ℝ) (νBound : ℚ) (hν : ‖ν‖ ≤ (νBound:ℝ))
    (M : Machine) (w : M.Input) :
    JetControl (addressedForce ν M w) (forceJetBound (M.scaleData w) νBound) := by
  let U := velocityJetBound (M.scaleData w)
  have hu : JetControl (addressedVelocity M w) U := addressedVelocity_jetControl M w
  have hproj (i : Fin 3) : ‖(EuclideanSpace.proj i : Space →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simpa using PiLp.norm_apply_le v i)
  have ha : JetControl (advection (addressedVelocity M w))
      (fun J k => 3*(2^k * ∑ i ∈ Finset.range (k+1), U J i * U 0 (k-i+1))) := by
    have h := JetControl.sum Finset.univ (fun i _ =>
      (hu.postcomp (EuclideanSpace.proj i) (hproj i)).smul (hu.spatialD i))
    convert h using 1 <;> first | rfl | simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hl : JetControl (laplace (addressedVelocity M w)) (fun J k => 3 * U J (k+1+1)) := by
    have h := JetControl.sum Finset.univ (fun i _ => (hu.spatialD i).spatialD i)
    convert h using 1 <;> first | rfl | simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  exact (hu.timeD.add ha).sub (hl.const_smul ν νBound hν)

end RapidForcing

end OAI
