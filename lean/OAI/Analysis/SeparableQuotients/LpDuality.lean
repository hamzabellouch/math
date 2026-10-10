import OAI.Analysis.SeparableQuotients.BranchSeparation

namespace OAI

noncomputable section

namespace SeparableQuotient.LpCoding
open Filter
open scoped Classical Topology ENNReal
universe u v
variable {ι : Type u} {p q : ℝ≥0∞}

def finite (p : ℝ≥0∞) : (ι →₀ ℝ) →ₗ[ℝ] lp (fun _ : ι => ℝ) p where
  toFun c := ⟨fun i => c i, Memℓp.of_exponent_ge (memℓp_zero_iff.mpr c.hasFiniteSupport) (zero_le (a := p))⟩
  map_add' _ _ := by apply lp.ext; funext i; rfl
  map_smul' _ _ := by apply lp.ext; funext i; rfl

@[simp] lemma finite_apply (p : ℝ≥0∞) (c : ι →₀ ℝ) (i : ι) : finite p c i = c i := rfl

@[simp] lemma finite_single (p : ℝ≥0∞) (i : ι) (a : ℝ) :
    finite p (Finsupp.single i a) = lp.single p i a := by
  apply lp.ext
  funext j
  simp [lp.single_apply,Finsupp.single_apply,Pi.single_apply,eq_comm]

lemma norm_finite (hp : 0 < p.toReal) (c : ι →₀ ℝ) :
    ‖finite p c‖ = (∑ i ∈ c.support, |c i| ^ p.toReal) ^ (1/p.toReal) := by
  rw [lp.norm_eq_tsum_rpow hp]
  congr 1
  simp only [finite_apply,Real.norm_eq_abs]
  apply tsum_eq_sum
  intro i hi
  simp [Finsupp.notMem_support_iff.mp hi,hp.ne']

lemma finite_dense [Fact (1 ≤ p)] (hp : p ≠ ∞) : DenseRange (finite p : (ι →₀ ℝ) → _) := by
  intro x
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single hp x)
  apply Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ i ∈ s, Finsupp.single i (x i),?_⟩
  simp

/-- The finite-support formulation of the norm of an ℓp dual element. -/
lemma finite_dual_bound (hpq : p.toReal.HolderConjugate q.toReal)
    (C : ℝ) (hC : 0 ≤ C) (a : ι → ℝ)
    (h : ∀ c : ι →₀ ℝ, |c.sum (fun i t => t*a i)| ≤ C*‖finite p c‖)
    (s : Finset ι) : ∑ i ∈ s, |a i| ^ q.toReal ≤ C ^ q.toReal := by
  let sign : ℝ → ℝ := fun t => if 0 ≤ t then 1 else -1
  have sign_abs (t : ℝ) : |sign t| = 1 := by dsimp [sign]; split_ifs <;> norm_num
  have sign_mul (t : ℝ) : sign t*t = |t| := by
    dsimp [sign]; split_ifs with ht
    · simp [abs_of_nonneg ht]
    · simp [abs_of_neg (lt_of_not_ge ht)]
  let c : ι →₀ ℝ := Finsupp.onFinset s
    (fun i => if i ∈ s then sign (a i)*|a i|^(q.toReal-1) else 0)
    (fun i hi => by by_contra hn; exact hi (ite_eq_right hn))
  have ci (i : ι) : c i = if i ∈ s then sign (a i)*|a i|^(q.toReal-1) else 0 := rfl
  let A : ℝ := ∑ i ∈ s, |a i|^q.toReal
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hpow (i : ι) : |sign (a i)*|a i|^(q.toReal-1)|^p.toReal = |a i|^q.toReal := by
    rw [abs_mul,sign_abs,one_mul,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      ← Real.rpow_mul (abs_nonneg _),hpq.symm.sub_one_mul_conj]
  have hc : ‖finite p c‖ = A^(1/p.toReal) := by
    rw [lp.norm_eq_tsum_rpow hpq.pos]
    congr 1
    calc
      _ = ∑ i ∈ s, |c i|^p.toReal := by
        simp only [finite_apply,Real.norm_eq_abs]
        apply tsum_eq_sum
        intro i hi
        simp only [ci,ite_eq_right hi,abs_zero,Real.zero_rpow hpq.ne_zero]
      _ = A := Finset.sum_congr rfl (fun i hi => by rw [ci,ite_eq_left hi,hpow])
  have hpair : c.sum (fun i t => t*a i) = A := by
    rw [Finsupp.sum_of_support_subset c (show c.support ⊆ s from by
      intro i hi; by_contra hn; exact Finsupp.mem_support_iff.mp hi (by rw [ci,ite_eq_right hn]))
      (fun i t => t*a i) (fun i _ => zero_mul _)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ci,ite_eq_left hi]
    calc
      sign (a i)*|a i|^(q.toReal-1)*a i = |a i|^(q.toReal-1)*|a i| := by rw [← sign_mul]; ring
      _ = |a i|^q.toReal := by
        rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith [hpq.symm.pos])]
        congr 1
        ring
  have hb := h c
  rw [hpair,abs_of_nonneg hA,hc] at hb
  by_cases hAz : A=0
  · rw [show (∑ i ∈ s, |a i|^q.toReal)=0 from hAz]
    exact Real.rpow_nonneg hC _
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hnorm : A^(1/q.toReal) ≤ C := by
    have hexp : 1/q.toReal = 1-1/p.toReal := by simpa only [one_div] using hpq.one_sub_inv.symm
    rw [hexp,Real.rpow_sub hAp,Real.rpow_one]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hAp _)).mpr hb
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg hA _) hnorm hpq.symm.pos.le
  simpa only [← Real.rpow_mul hA,one_div_mul_cancel hpq.symm.ne_zero,Real.rpow_one] using hr

lemma dual_mem (hpq : p.toReal.HolderConjugate q.toReal)
    (C : ℝ) (hC : 0 ≤ C) (a : ι → ℝ)
    (h : ∀ c : ι →₀ ℝ, |c.sum (fun i t => t*a i)| ≤ C*‖finite p c‖) : Memℓp a q := by
  apply memℓp_gen'
  simpa only [Real.norm_eq_abs] using finite_dual_bound hpq C hC a h

lemma dual_norm (hpq : p.toReal.HolderConjugate q.toReal)
    (C : ℝ) (hC : 0 ≤ C) (a : ι → ℝ)
    (h : ∀ c : ι →₀ ℝ, |c.sum (fun i t => t*a i)| ≤ C*‖finite p c‖) :
    ‖(⟨a,dual_mem hpq C hC a h⟩ : lp (fun _ : ι => ℝ) q)‖ ≤ C := by
  apply lp.norm_le_of_forall_sum_le hpq.symm.pos hC
  simpa only [Real.norm_eq_abs] using finite_dual_bound hpq C hC a h

end SeparableQuotient.LpCoding

namespace SeparableQuotient.LpCoding
open Filter
open scoped Classical Topology ENNReal
universe u v
variable {ι : Type u} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
lemma single_eq_smul (p : ℝ≥0∞) (i : ι) (a : ℝ) :
    lp.single (E := fun _ : ι => ℝ) p i a = a • lp.single p i (1 : ℝ) := by
  simpa only [smul_eq_mul,mul_one] using (lp.single_smul (E := fun _ : ι => ℝ) (𝕜 := ℝ) p i a (1 : ℝ))

lemma coefficient_bound (g : StrongDual ℝ (lp (fun _ : ι => ℝ) p)) (c : ι →₀ ℝ) :
    |c.sum (fun i t => t*g (lp.single p i 1))| ≤ ‖g‖ * ‖finite p c‖ := by
  have he : c.sum (fun i t => t*g (lp.single p i 1)) = g (finite p c) := by
    conv_rhs => rw [← Finsupp.sum_single c]
    simp only [map_finsuppSum,finite_single]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only
    rw [single_eq_smul p i (c i),map_smul,smul_eq_mul]
  rw [he]
  exact g.le_opNorm _

def coefficients (hpq : p.toReal.HolderConjugate q.toReal)
    (g : StrongDual ℝ (lp (fun _ : ι => ℝ) p)) : lp (fun _ : ι => ℝ) q :=
  ⟨fun i => g (lp.single p i 1),
    dual_mem hpq ‖g‖ (norm_nonneg _) _ (coefficient_bound g)⟩

omit [Fact (1 ≤ q)] in
@[simp] lemma coefficients_apply (hpq : p.toReal.HolderConjugate q.toReal)
    (g : StrongDual ℝ (lp (fun _ : ι => ℝ) p)) (i : ι) :
    coefficients hpq g i = g (lp.single p i 1) := rfl

omit [Fact (1 ≤ q)] in
lemma norm_coefficients_le (hpq : p.toReal.HolderConjugate q.toReal)
    (g : StrongDual ℝ (lp (fun _ : ι => ℝ) p)) : ‖coefficients hpq g‖ ≤ ‖g‖ :=
  dual_norm hpq ‖g‖ (norm_nonneg _) _ (coefficient_bound g)

def coefficientMap (hpq : p.toReal.HolderConjugate q.toReal) :
    StrongDual ℝ (lp (fun _ : ι => ℝ) p) →L[ℝ] lp (fun _ : ι => ℝ) q :=
  LinearMap.mkContinuous
    { toFun := coefficients hpq
      map_add' := fun _ _ => by apply lp.ext; rfl
      map_smul' := fun _ _ => by apply lp.ext; rfl }
    1 (fun g => by simpa using norm_coefficients_le hpq g)

@[simp] lemma coefficientMap_apply (hpq : p.toReal.HolderConjugate q.toReal)
    (g : StrongDual ℝ (lp (fun _ : ι => ℝ) p)) (i : ι) :
    coefficientMap hpq g i = g (lp.single p i 1) := rfl

lemma norm_coefficientMap_le (hpq : p.toReal.HolderConjugate q.toReal) :
    ‖coefficientMap (ι := ι) hpq‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro g
  change ‖coefficients hpq g‖ ≤ 1*‖g‖
  simpa using norm_coefficients_le hpq g

/-- Symmetry of the two ℓp dual evaluations. -/
lemma eval_coefficients_symm (hpq : p.toReal.HolderConjugate q.toReal)
    (hp : p ≠ ∞) (hq : q ≠ ∞)
    (g : StrongDual ℝ (lp (fun _ : ι => ℝ) p))
    (h : StrongDual ℝ (lp (fun _ : ι => ℝ) q)) :
    g (coefficients hpq.symm h) = h (coefficients hpq g) := by
  have hg := g.continuous.tendsto _ |>.comp
    (lp.hasSum_single hp (coefficients hpq.symm h))
  have hh := h.continuous.tendsto _ |>.comp
    (lp.hasSum_single hq (coefficients hpq g))
  have he : (fun s : Finset ι => g (∑ i ∈ s, lp.single p i (coefficients hpq.symm h i))) =
      (fun s : Finset ι => h (∑ i ∈ s, lp.single q i (coefficients hpq g i))) := by
    funext s
    simp only [map_sum,coefficients_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [single_eq_smul p i (h (lp.single q i 1)),
      single_eq_smul q i (g (lp.single p i 1))]
    simp only [map_smul,smul_eq_mul,mul_comm]
  exact tendsto_nhds_unique hg (by simpa only [Function.comp_def,← he] using hh)

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

def analysisMap (hpq : p.toReal.HolderConjugate q.toReal)
    (T : lp (fun _ : ι => ℝ) p →L[ℝ] E) : StrongDual ℝ E →L[ℝ] lp (fun _ : ι => ℝ) q :=
  LinearMap.mkContinuous
    { toFun := fun g => coefficients hpq (g.comp T)
      map_add' := fun g h => by apply lp.ext; rfl
      map_smul' := fun c g => by apply lp.ext; rfl }
    ‖T‖ (fun g => (norm_coefficients_le hpq (g.comp T)).trans
      (by simpa only [mul_comm] using ContinuousLinearMap.opNorm_comp_le g T))

@[simp] lemma analysisMap_apply (hpq : p.toReal.HolderConjugate q.toReal)
    (T : lp (fun _ : ι => ℝ) p →L[ℝ] E) (g : StrongDual ℝ E) (i : ι) :
    analysisMap hpq T g i = g (T (lp.single p i 1)) := rfl

lemma norm_analysisMap_le (hpq : p.toReal.HolderConjugate q.toReal)
    (T : lp (fun _ : ι => ℝ) p →L[ℝ] E) : ‖analysisMap hpq T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro g
  change ‖coefficients hpq (g.comp T)‖ ≤ _
  exact (norm_coefficients_le hpq (g.comp T)).trans
    (by simpa only [mul_comm] using ContinuousLinearMap.opNorm_comp_le g T)

end SeparableQuotient.LpCoding

end

end OAI
