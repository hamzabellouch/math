import OAI.MathematicalPhysics.Elasticity.Carleman

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
namespace ElasticityRegularity

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma fourierMultiplier_add {g h : E → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    fourierMultiplierCLM F (g+h) u=fourierMultiplierCLM F g u+fourierMultiplierCLM F h u := by
  simp only [fourierMultiplierCLM_apply,smulLeftCLM_add hg hh,add_apply,fourierInv_add]

omit [CompleteSpace F] in
lemma besselPotential_two (u : 𝓢'(E,F)) :
    besselPotential E F 2 u=u+fourierMultiplierCLM F (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) u := by
  have he : (fun x : E => (((1+‖x‖^2)^(2/2 : ℝ) : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ))+(fun x : E => ((‖x‖^2 : ℝ) : ℂ)) := by
    funext x
    norm_num
  rw [besselPotential,he,fourierMultiplier_add (by fun_prop) (by fun_prop)]
  simp

lemma sobolev_real_smul {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (c : ℝ) :
    MemSobolev s 2 (c • u) := by
  convert hu.smul (c : ℂ) using 1

/-- Whole-space elliptic gain for the actual distributional Laplacian. -/
theorem laplacian_gain {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hΔ : MemSobolev s 2 (Δ u)) : MemSobolev (s+2) 2 u := by
  have hp : (-(2*Real.pi)^2 : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hm := sobolev_real_smul hΔ (-(2*Real.pi)^2)⁻¹
  rw [laplacian_eq_fourierMultiplierCLM,smul_smul,inv_mul_cancel₀ hp,one_smul] at hm
  have h := hu.add hm
  rw [← besselPotential_two,memSobolev_besselPotential_iff] at h
  simpa only [add_comm] using h

/-- One derivative of gain from information on all coordinate first derivatives. -/
theorem coordinate_derivative_gain {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hd : ∀ i, MemSobolev s 2 (∂_{b i} u)) :
    MemSobolev (s+1) 2 u := by
  have hall : ∀ S : Finset ι, MemSobolev (s-1) 2 (∑ i ∈ S, ∂_{b i} (∂_{b i} u)) := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi hS =>
      rw [Finset.sum_insert hi]
      exact ((hd i).lineDerivOp).add hS
  have hsum := hall Finset.univ
  rw [← laplacian_eq_sum b] at hsum
  have h := laplacian_gain (hu.mono (by linarith : s-1 ≤ s)) hsum
  have he : s-1+2=s+1 := by ring
  rwa [he] at h

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma compact_derivative {g : E → ℂ} (hg : HasCompactSupport g) (m : E) :
    HasCompactSupport (fun x => fderiv ℝ g x m) :=
  (hg.fderiv ℝ).comp_left (g := fun T : E →L[ℝ] ℂ => T m) (by simp)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma smooth_derivative {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ g x m) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma schwartz_leibniz {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (m : E) (hd : (fun x => fderiv ℝ g x m).HasTemperateGrowth) (φ : 𝓢(E,ℂ)) :
    ∂_{m} (SchwartzMap.smulLeftCLM ℂ g φ) =
      SchwartzMap.smulLeftCLM ℂ (fun x => fderiv ℝ g x m) φ +
        SchwartzMap.smulLeftCLM ℂ g (∂_{m} φ) := by
  ext x
  simp only [add_apply,SchwartzMap.smulLeftCLM_apply_apply hd,
    SchwartzMap.smulLeftCLM_apply_apply hg,SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.smulLeftCLM_apply hg]
  change fderiv ℝ (g*(φ : E → ℂ)) x m =
    fderiv ℝ g x m*φ x+g x*fderiv ℝ (φ : E → ℂ) x m
  rw [fderiv_mul (hg.1.differentiable (by simp) x) φ.differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

omit [CompleteSpace F] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma distribution_leibniz {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (m : E) (hd : (fun x => fderiv ℝ g x m).HasTemperateGrowth) (u : 𝓢'(E,F)) :
    ∂_{m} (smulLeftCLM F g u) =
      smulLeftCLM F (fun x => fderiv ℝ g x m) u+smulLeftCLM F g (∂_{m} u) := by
  ext φ
  simp only [lineDerivOp_apply_apply,smulLeftCLM_apply_apply,add_apply,
    schwartz_leibniz hg m hd,map_neg,map_add]
  abel

lemma compact_bounded_multiplier {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) : MemLp g ∞ (volume : Measure E) := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn hg.continuous.continuousOn
  refine memLp_top_of_bound hg.continuous.aestronglyMeasurable (max C 0)
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport g
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact le_max_right _ _

lemma sobolev_zero_product {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hb : MemLp g ∞ (volume : Measure E)) {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (smulLeftCLM F g u) := by
  obtain ⟨v,rfl⟩ := memSobolev_zero_iff.mp hu
  apply memSobolev_zero_iff.mpr
  exact ⟨hb.toLp g • v, (Lp.toTemperedDistribution_smul_eq hg hb v).symm⟩

/-- Smooth compact coefficients preserve every nonnegative integral Sobolev order.
This is proved for the actual tempered distribution product, not an assumed
bounded multiplier on an unspecified Sobolev completion. -/
theorem sobolev_nat_product {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (n : ℕ) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    {u : 𝓢'(E,F)} (hu : MemSobolev n 2 u) : MemSobolev n 2 (smulLeftCLM F g u) := by
  induction n generalizing u g with
  | zero =>
    rw [Nat.cast_zero] at hu ⊢
    exact sobolev_zero_product (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) hu
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one] at hu ⊢
    apply coordinate_derivative_gain b (ih hg hc (hu.mono (by norm_num)))
    intro i
    have hd : MemSobolev (n : ℝ) 2 (∂_{b i} u) := by
      simpa only [add_sub_cancel_right] using hu.lineDerivOp (m := b i)
    rw [distribution_leibniz (hc.hasTemperateGrowth hg) (b i)
      ((compact_derivative hc (b i)).hasTemperateGrowth (smooth_derivative hg (b i)))]
    exact (ih (smooth_derivative hg (b i)) (compact_derivative hc (b i))
      (hu.mono (by norm_num))).add (ih hg hc hd)

lemma sobolev_zero_product_derivative {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (m : E) {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev (-1) 2 (smulLeftCLM F g (∂_{m} u)) := by
  have h1 := (sobolev_zero_product (hc.hasTemperateGrowth hg)
    (compact_bounded_multiplier hg hc) hu).lineDerivOp (m := m)
  simp only [zero_sub] at h1
  have h2 := sobolev_zero_product
    ((compact_derivative hc m).hasTemperateGrowth (smooth_derivative hg m))
    (compact_bounded_multiplier (smooth_derivative hg m) (compact_derivative hc m)) hu
  have h := h1.sub (h2.mono (by norm_num : (-1 : ℝ) ≤ 0))
  rw [distribution_leibniz (hc.hasTemperateGrowth hg) m
    ((compact_derivative hc m).hasTemperateGrowth (smooth_derivative hg m)),add_sub_cancel_left] at h
  exact h

end ElasticityRegularity

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityDistribution

open ElasticityAugmented ElasticityRegularity TemperedDistribution
abbrev X := ElasticityAugmented.X
abbrev Dist := 𝓢'(X,ℂ)

/-- Smooth temperate coefficients act on actual tempered distributions. -/
def coefficientAlgebra : Subalgebra ℂ Smooth where
  carrier := {a | (a : X → ℂ).HasTemperateGrowth}
  add_mem' ha hb := ha.add hb
  mul_mem' ha hb := ha.mul hb
  zero_mem' := Function.HasTemperateGrowth.zero
  one_mem' := Function.HasTemperateGrowth.const 1
  algebraMap_mem' c := Function.HasTemperateGrowth.const c
abbrev Coeff := coefficientAlgebra

def eval (a : Coeff) : X → ℂ := a.val
lemma growth (a : Coeff) : (eval a).HasTemperateGrowth := a.property
lemma eval_smooth (a : Coeff) : ContDiff ℝ (⊤ : ℕ∞) (eval a) := (growth a).1

@[simp] lemma eval_add (a b : Coeff) : eval (a+b) = eval a+eval b := rfl
@[simp] lemma eval_mul (a b : Coeff) : eval (a*b) = eval a*eval b := rfl
@[simp] lemma eval_one : eval (1 : Coeff) = fun _ => 1 := rfl

instance : SMul Coeff Dist := ⟨fun a u => smulLeftCLM ℂ (eval a) u⟩
lemma smul_def (a : Coeff) (u : Dist) : a • u = smulLeftCLM ℂ (eval a) u := rfl
instance : Module Coeff Dist := Module.ofMinimalAxioms
  (fun a u v => (smulLeftCLM ℂ (eval a)).map_add u v)
  (fun a b u => by simp only [smul_def, eval_add, smulLeftCLM_add (growth a) (growth b),
    add_apply])
  (fun a b u => by
    simp only [smul_def, eval_mul]
    rw [smulLeftCLM_smulLeftCLM_apply (growth b) (growth a),mul_comm])
  (fun u => by simp only [smul_def,eval_one,smulLeftCLM_const,one_smul])

instance : IsScalarTower ℂ Coeff Dist where
  smul_assoc c a u := by
    change smulLeftCLM ℂ (c • eval a) u = c • smulLeftCLM ℂ (eval a) u
    rw [smulLeftCLM_smul (growth a) c, smul_apply]
instance : SMulCommClass ℂ Coeff Dist where
  smul_comm c a u := ((smulLeftCLM ℂ (eval a)).map_smul c u).symm

/-- The coefficient derivative and distribution derivative are genuine derivatives. -/
def dc (i : Fin 3) : Derivation ℂ Coeff Coeff := Derivation.mk' (R := ℂ) (A := Coeff) (M := Coeff)
  ({ toFun := fun (a : Coeff) => (⟨coord i a.val, ElasticityPhysicalAlgebra.temperate_partial _ (growth a) (e i)⟩ : Coeff)
     map_add' a b := by apply Subtype.ext; exact map_add (coord i) _ _
     map_smul' c a := by apply Subtype.ext; exact (coord i).toLinearMap.map_smul c a.val } : Coeff →ₗ[ℂ] Coeff)
  (by intro (a : Coeff) (b : Coeff); apply Subtype.ext; exact (coord i).leibniz a.val b.val)

def dd (i : Fin 3) : Dist →ₗ[ℂ] Dist := (LineDeriv.lineDerivOpCLM ℂ Dist (e i)).toLinearMap
lemma dd_apply (i : Fin 3) (u : Dist) : dd i u = ∂_{e i} u := rfl
lemma dc_eval (i : Fin 3) (a : Coeff) : eval (dc i a) = fun x => fderiv ℝ (eval a) x (e i) := rfl
lemma dc_commute (i j : Fin 3) (a : Coeff) : dc i (dc j a) = dc j (dc i a) := by
  apply Subtype.ext
  exact coord_commute i j a.val
lemma dd_commute (i j : Fin 3) (u : Dist) : dd i (dd j u) = dd j (dd i u) := by
  ext φ
  change u (- ∂_{e j} (- ∂_{e i} φ)) = u (- ∂_{e i} (- ∂_{e j} φ))
  simp only [LineDeriv.lineDerivOp_neg,neg_neg]
  congr 1
  exact ElasticitySchwartzCarleman.d_comm (e j) (e i) φ
lemma dd_leibniz (i : Fin 3) (a : Coeff) (u : Dist) :
    dd i (a • u) = dc i a • u+a • dd i u := by
  exact distribution_leibniz (growth a) (e i) (growth (dc i a)) u

open ElasticityAugmented TrivSqZeroExt

instance : SMul Coeffᵐᵒᵖ Dist := ⟨fun a u => a.unop • u⟩
instance : Module Coeffᵐᵒᵖ Dist := Module.ofMinimalAxioms
  (fun a u v => smul_add a.unop u v)
  (fun a b u => add_smul a.unop b.unop u)
  (fun a b u => by change (b.unop*a.unop) • u = a.unop • b.unop • u; rw [mul_comm,mul_smul])
  (fun u => (one_smul Coeff u))
instance : IsCentralScalar Coeff Dist where
  op_smul_eq_smul _a _u := rfl
instance : IsScalarTower ℂ Coeffᵐᵒᵖ Dist where
  smul_assoc c a u := by change (c • a.unop) • u = c • a.unop • u; exact smul_assoc c a.unop u

abbrev Ext := TrivSqZeroExt Coeff Dist
/-- The square-zero algebra is only an algebraic way of reusing the physical
compatibility identities: its genuine distribution component is never multiplied
by another distribution. -/
def de (i : Fin 3) : Derivation ℂ Ext Ext := Derivation.mk' (R := ℂ) (A := Ext) (M := Ext)
  ({ toFun := fun v => (dc i v.fst,dd i v.snd)
     map_add' := by
       intro v w
       apply TrivSqZeroExt.ext
       · change dc i (v.fst+w.fst) = dc i v.fst+dc i w.fst
         exact map_add (dc i) _ _
       · change dd i (v.snd+w.snd) = dd i v.snd+dd i w.snd
         exact map_add (dd i) _ _
     map_smul' := by
       intro c v
       apply TrivSqZeroExt.ext
       · change dc i (c • v.fst) = c • dc i v.fst
         exact (dc i).map_smul c v.fst
       · change dd i (c • v.snd) = c • dd i v.snd
         exact (dd i).map_smul c v.snd } : Ext →ₗ[ℂ] Ext)
  (by
    intro v w
    apply TrivSqZeroExt.ext
    · change dc i (v.fst*w.fst) = v.fst*dc i w.fst+w.fst*dc i v.fst
      exact (dc i).leibniz _ _
    · change dd i (v.fst • w.snd+w.fst • v.snd) =
        v.fst • dd i w.snd+dc i w.fst • v.snd +
        (w.fst • dd i v.snd+dc i v.fst • w.snd)
      rw [map_add,dd_leibniz,dd_leibniz]
      abel)
lemma de_fst (i : Fin 3) (v : Ext) : (de i v).fst = dc i v.fst := rfl
lemma de_snd (i : Fin 3) (v : Ext) : (de i v).snd = dd i v.snd := rfl
lemma de_inl (i : Fin 3) (a : Coeff) : de i (inl a) = inl (dc i a) := by
  apply TrivSqZeroExt.ext <;> simp [de_fst,de_snd]
lemma de_inr (i : Fin 3) (u : Dist) : de i (inr u) = inr (dd i u) := by
  apply TrivSqZeroExt.ext <;> simp [de_fst,de_snd]
lemma de_commute (i j : Fin 3) (v : Ext) : de i (de j v) = de j (de i v) := by
  apply TrivSqZeroExt.ext
  · exact dc_commute i j v.fst
  · exact dd_commute i j v.snd

def sd (z : Fin 3 → ℂ) (i : Fin 3) : Dist →ₗ[ℂ] Dist := dd i+z i • LinearMap.id
lemma sd_apply (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) : sd z i u = dd i u+z i • u := rfl
lemma shifted_inr (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) :
    shifted (A := Ext) de z i (inr u) = inr (sd z i u) := by
  simp only [shifted_apply,sd_apply,de_inr,inr_add,inr_smul]

def lapd (z : Fin 3 → ℂ) (u : Dist) : Dist := ∑ i, sd z i (sd z i u)
def divd (z : Fin 3 → ℂ) (u : Fin 3 → Dist) : Dist := ∑ i, sd z i (u i)
def rd (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (d : Dist) (i : Fin 3) : Dist :=
  m • lapd z (u i)+(lam+m) • sd z i d+
    (∑ j, dc j m • (sd z j (u i)+sd z i (u j)))+dc i lam • d

def scd (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (d : Dist) : Dist :=
  (lam+m+m) • lapd z d + (2 : ℂ) • (∑ i, dc i (lam+m) • sd z i d) +
  (2 : ℂ) • (∑ i, dc i m • lapd z (u i))+
  (2 : ℂ) • (∑ i, ∑ j, dc i (dc j m) • sd z i (u j))+
  (∑ i, dc i (dc i lam)) • d

def phys (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (i : Fin 3) : Dist :=
  sd z i (lam • divd z u)+ ∑ j, sd z j (m • (sd z j (u i)+sd z i (u j)))

lemma lapT_inr (z : Fin 3 → ℂ) (u : Dist) :
    lapT (shifted (A := Ext) de z) (inr u) = inr (lapd z u) := by
  simp only [lapT,lapd,shifted_inr,inr_sum]
lemma divT_inr (z : Fin 3 → ℂ) (u : Fin 3 → Dist) :
    divT (shifted (A := Ext) de z) (fun i => inr (u i)) = inr (divd z u) := by
  simp only [divT,divd,shifted_inr,inr_sum]
lemma LT_inr (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (i : Fin 3) :
    LT (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) i = inr (phys z lam m u i) := by
  simp only [ElasticityAugmented.LT,phys,divT_inr,shifted_inr,inl_mul_inr,← inr_add,← inr_sum]
lemma RT_inr (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (d : Dist) (i : Fin 3) :
    RT de (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) (inr d) i =
      inr (rd z lam m u d i) := by
  simp only [RT,cmT,rd,lapT_inr,shifted_inr,de_inl,← inl_add,inl_mul_inr,← inr_add,← inr_sum]
lemma ST_inr (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (d : Dist) :
    ST de (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) (inr d) =
      inr (scd z lam m u d) := by
  simp only [ElasticityAugmented.ST,scd,lap,lapT_inr,shifted_inr,de_inl,← inl_add,inl_mul_inr,
    ← inl_sum,← inr_sum]
  simp only [two_mul,← inr_add]
  congr 1
  ext φ
  simp only [add_apply]
  change _ = _ + (2 : ℂ) * ((∑ i, dc i (lam+m) • sd z i d) φ) +
    (2 : ℂ) * ((∑ i, dc i m • lapd z (u i)) φ) +
    (2 : ℂ) * ((∑ i, ∑ j, dc i (dc j m) • sd z i (u j)) φ) + _
  ring

/-- The genuine distributional physical equation has the same compatible
augmented scalar-principal system as the smooth equation. No regularity of the
unknown is used in this differential identity. -/
theorem physical_expansion (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (i : Fin 3) :
    phys z lam m u i = rd z lam m u (divd z u) i := by
  have h := shifted_physical_expansion de z (inl lam) (inl m) (fun j => inr (u j)) de_commute i
  rw [LT_inr,divT_inr,RT_inr] at h
  exact congrArg TrivSqZeroExt.snd h

theorem physical_divergence (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) :
    divd z (phys z lam m u) = scd z lam m u (divd z u) := by
  have h := shifted_physical_divergence de z (inl lam) (inl m) (fun j => inr (u j)) de_commute
  have hL : ElasticityAugmented.LT (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) =
      (fun i => inr (phys z lam m u i)) := funext (LT_inr z lam m u)
  rw [hL,divT_inr,divT_inr,ST_inr] at h
  exact congrArg TrivSqZeroExt.snd h

def normPair (z : Fin 3 → ℂ) (lam m n o : Coeff) (u : Fin 3 → Dist) (d : Dist) : Fin 4 → Dist :=
  Fin.cons (o • (scd z lam m u d-(2 : ℂ) • (n • (∑ i, dc i m • rd z lam m u d i))))
    (fun i => n • rd z lam m u d i)
lemma inl_two : inl (2 : Coeff) = (2 : Ext) := by
  exact inl_natCast 2
lemma coff_inl_mul (a b : Coeff) : (inl a : Ext)*inl b = inl (a*b) :=
  (inl_mul Dist a b).symm
lemma coff_inl_add (a b : Coeff) : (inl a : Ext)+inl b = inl (a+b) :=
  (inl_add Dist a b).symm
lemma coff_inl_sub (a b : Coeff) : (inl a : Ext)-inl b = inl (a-b) :=
  (inl_sub Dist a b).symm
lemma dist_inr_sub (u v : Dist) : (inr u : Ext)-inr v = inr (u-v) :=
  (inr_sub Coeff u v).symm
lemma coeff_two_smul (u : Dist) : (2 : Coeff) • u = (2 : ℂ) • u := by
  change TemperedDistribution.smulLeftCLM ℂ (fun _ : X => (2 : ℂ)) u = _
  rw [TemperedDistribution.smulLeftCLM_const]

lemma coeffA_inl (lam m n o : Coeff) (k : Fin 3) (i j : Fin 4) :
    coeffA (A := Ext) de (inl lam) (inl m) (inl n) (inl o) k i j = inl (coeffA dc lam m n o k i j) := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [coeffA,Fin.cons_zero,Fin.cons_succ,coff_inl_add,de_inl,coff_inl_mul,
      coff_inl_sub,← inl_two]
  · split_ifs <;> rfl
  · split_ifs <;> simp only [coff_inl_add,add_zero,zero_add,inl_zero]
lemma coeffV_inl (lam m n o : Coeff) (i j : Fin 4) :
    coeffV (A := Ext) de (inl lam) (inl m) (inl n) (inl o) i j = inl (coeffV dc lam m n o i j) := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [coeffV,lap,Fin.cons_zero,Fin.cons_succ,de_inl,coff_inl_mul,← inl_sum,
      coff_inl_sub,← inl_two,inl_zero]
lemma normalizedPair_inr (z : Fin 3 → ℂ) (lam m n o : Coeff) (u : Fin 3 → Dist) (d : Dist) (i : Fin 4) :
    normalizedPair de (shifted (A := Ext) de z) (inl lam) (inl m) (inl n) (inl o) (fun j => inr (u j)) (inr d) i =
      inr (normPair z lam m n o u d i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [normalizedPair,normPair,Fin.cons_zero,ST_inr,RT_inr,de_inl,inl_mul_inr,
      ← inr_sum]
    rw [← inl_two,coff_inl_mul,inl_mul_inr,dist_inr_sub,inl_mul_inr]
    congr 1
    congr 1
    congr 1
    exact (mul_smul (2 : Coeff) n (∑ i, dc i m • rd z lam m u d i)).trans (coeff_two_smul _)
  · simp only [normalizedPair,normPair,Fin.cons_succ,RT_inr,inl_mul_inr]

/-- Genuine scalar-principal matrix form for the actual distribution system. -/
theorem normalized_matrix (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (hn : n*m=1) (ho : o*(lam+m+m)=1) (U : Fin 4 → Dist) (i : Fin 4) :
    normPair z lam m n o (fun j => U j.succ) (U 0) i =
      lapd z (U i)+(∑ k, ∑ j, coeffA dc lam m n o k i j • sd z k (U j))+
        (∑ j, coeffV dc lam m n o i j • U j) := by
  have hn' : (inl n : Ext)*inl m=1 := by rw [coff_inl_mul,hn]; rfl
  have ho' : (inl o : Ext)*(inl lam+inl m+inl m)=1 := by
    rw [coff_inl_add,coff_inl_add,coff_inl_mul,ho]; rfl
  have h := normalizedPair_matrix de (shifted (A := Ext) de z) (inl lam) (inl m) (inl n) (inl o)
    hn' ho' (fun j => inr (U j)) i
  simp only [normalizedPair_inr,lapT_inr,coeffA_inl,coeffV_inl,shifted_inr,inl_mul_inr,
    ← inr_sum,← inr_add] at h
  exact congrArg TrivSqZeroExt.snd h
end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity


section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma sobolev_sum {ι : Type*} (S : Finset ι) {s : ℝ} {v : ι → 𝓢'(E,F)}
    (hv : ∀ i ∈ S, MemSobolev s 2 (v i)) : MemSobolev s 2 (∑ i ∈ S, v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi hS =>
    rw [Finset.sum_insert hi]
    exact (hv i (Finset.mem_insert_self _ _)).add
      (hS (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

/-- Actual all-order elliptic bootstrap for scalar-principal systems.  The
unknown is only assumed to be represented by L2; its derivatives are the actual
tempered-distribution derivatives.  Compact smooth coefficients are sufficient
for the localized physical augmented and planar systems. -/
theorem elliptic_all_orders {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ E) (a : κ → κ → ι → E → ℂ) (c : κ → κ → E → ℂ)
    (ha : ∀ i j d, ContDiff ℝ (⊤ : ℕ∞) (a i j d)) (hac : ∀ i j d, HasCompactSupport (a i j d))
    (hc : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (c i j)) (hcc : ∀ i j, HasCompactSupport (c i j))
    (f : κ → 𝓢(E,F)) (u : κ → 𝓢'(E,F)) (hu : ∀ i, MemSobolev 0 2 (u i))
    (heq : ∀ i, Δ (u i) = (∑ j, ∑ d, smulLeftCLM F (a i j d) (∂_{b d} (u j)))+
      (∑ j, smulLeftCLM F (c i j) (u j))+(f i : 𝓢'(E,F))) :
    ∀ n : ℕ, ∀ i, MemSobolev n 2 (u i) := by
  classical
  intro n
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact hu
  | succ n ih =>
    cases n with
    | zero =>
      intro i
      have hd : MemSobolev (-1) 2 (Δ (u i)) := by
        rw [heq]
        refine ((sobolev_sum Finset.univ (fun j _ =>
          sobolev_sum Finset.univ (fun d _ =>
            sobolev_zero_product_derivative (ha i j d) (hac i j d) (b d) (hu j)))).add ?_).add
          ((f i).memSobolev (s := -1) (p := 2))
        apply sobolev_sum Finset.univ
        intro j _
        exact (sobolev_zero_product ((hcc i j).hasTemperateGrowth (hc i j))
          (compact_bounded_multiplier (hc i j) (hcc i j)) (hu j)).mono (by norm_num)
      have hh := laplacian_gain ((hu i).mono (by norm_num : (-1 : ℝ) ≤ 0)) hd
      norm_num at hh ⊢
      exact hh
    | succ k =>
      intro i
      have hlow (j : κ) : MemSobolev (k : ℝ) 2 (u j) :=
        (ih j).mono (by simp)
      have hder (j : κ) (d : ι) : MemSobolev (k : ℝ) 2 (∂_{b d} (u j)) := by
        simpa using (ih j).lineDerivOp (m := b d)
      have hd : MemSobolev (k : ℝ) 2 (Δ (u i)) := by
        rw [heq]
        exact ((sobolev_sum Finset.univ (fun j _ => sobolev_sum Finset.univ
          (fun d _ => sobolev_nat_product b k (ha i j d) (hac i j d) (hder j d)))).add
          (sobolev_sum Finset.univ (fun j _ =>
            sobolev_nat_product b k (hc i j) (hcc i j) (hlow j)))).add (f i).memSobolev
      convert laplacian_gain (hlow i) hd using 1
      push_cast
      ring

lemma decay_memLp {s : ℝ} (hs : Module.finrank ℝ E < 2*s) :
    MemLp (fun x : E => (1+‖x‖^2)^(-s/2)) 2 := by
  have growth : (fun x : E => (1+‖x‖^2)^(-s/2)).HasTemperateGrowth := by fun_prop
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) growth.1.continuous.aestronglyMeasurable]
  suffices h : ∫⁻ x : E, ENNReal.ofReal ‖(1+‖x‖^2)^(-s)‖ < ⊤ from by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h
    rw [← Real.rpow_mul_natCast (by positivity)]
    simp
  apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weighted_decay_bound (x : E) (n k : ℕ) :
    ‖x‖^n*(1+‖x‖^2)^(-(n+k : ℝ)) ≤ (1+‖x‖^2)^(-(k : ℝ)) := by
  have hpos : 0 < 1+‖x‖^2 := by positivity
  have hbase : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
  calc
    _ ≤ (1+‖x‖^2)^n*(1+‖x‖^2)^(-(n+k : ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hbase n) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_add hpos]
      congr 1
      ring

lemma all_orders_fourier_moments {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolev n 2 u) :
    ∃ v : Lp F 1 (volume : Measure E), 𝓕 u = (v : 𝓢'(E,F)) ∧
      ∀ n : ℕ, Integrable (fun x => ‖x‖^n*‖v x‖) := by
  let k : ℕ := Module.finrank ℝ E+1
  have hk : (Module.finrank ℝ E : ℝ) < 2*k := by dsimp [k]; push_cast; linarith
  obtain ⟨v,hv⟩ := (hu k).fourier_memL1 hk
  refine ⟨v,hv,fun n => ?_⟩
  obtain ⟨w,hw⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp (hu (2*(n+k)))
  have hdec (m : ℕ) (hm : k ≤ m) : MemLp (fun x : E => (1+‖x‖^2)^(-(m : ℝ))) 2 := by
    have hh : (Module.finrank ℝ E : ℝ) < 2*(2*m) := by
      have : (k : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    convert decay_memLp hh using 1
    ext x
    congr 1
    ring
  have hg : MemLp (fun x : E => Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ)))) 2 :=
    (hdec (n+k) (Nat.le_add_left _ _)).ofReal
  let q : Lp F 1 (volume : Measure E) := hg.toLp _ • w
  have hq : (q : 𝓢'(E,F)) = 𝓕 u := by
    rw [Lp.toTemperedDistribution_smul_eq (by fun_prop),← hw,
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert (smulLeftCLM_const (1 : ℂ) (𝓕 u)) using 1
    · congr 2
      ext x
      change Complex.ofReal ((1+‖x‖^2)^((↑(2*(n+k)) : ℝ)/2)) *
        Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ))) = 1
      rw [← Complex.ofReal_mul,← Complex.ofReal_one,Complex.ofReal_inj]
      rw [← Real.rpow_add (by positivity : 0 < (1+‖x‖^2 : ℝ))]
      convert Real.rpow_zero (1+‖x‖^2) using 1
      congr 1
      push_cast
      ring
    · simp
  have heq : q=v := by
    apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F))
    change (q : 𝓢'(E,F)) = (v : 𝓢'(E,F))
    rw [hq,hv]
  have hqa : ∀ᵐ x, v x = Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ))) • w x := by
    rw [← heq]
    filter_upwards [Lp.coeFn_lpSMul (r := 1) (hg.toLp _) w, hg.coeFn_toLp] with x hx hy
    change q x = _ at hx
    rw [hx]
    change (hg.toLp _ : E → ℂ) x • w x = _
    rw [hy]
  have hi : Integrable (fun x : E => (1+‖x‖^2)^(-(k : ℝ))*‖w x‖) :=
    (hdec k le_rfl).integrable_mul (Lp.memLp w).norm
  apply hi.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable v).norm)
  filter_upwards [hqa] with x hx
  change ‖‖x‖^n*‖v x‖‖ ≤ _
  rw [hx,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),← mul_assoc]
  simpa only [Nat.cast_add] using
    mul_le_mul_of_nonneg_right (weighted_decay_bound x n k) (norm_nonneg (w x))

end

section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma l1_inverse_fourier_distribution (v : Lp F 1 (volume : Measure E)) :
    (((Real.Lp.fourierTransformInv v).memLp_top.toLp _ : Lp F ∞ (volume : Measure E)) : 𝓢'(E,F)) =
      𝓕⁻ (v : 𝓢'(E,F)) := by
  ext φ
  rw [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x : E, φ x • 𝓕⁻ (v : E → F) x := by
      apply integral_congr_ae
      filter_upwards [(Real.Lp.fourierTransformInv v).memLp_top.coeFn_toLp] with x hx
      rw [hx,Real.Lp.fourierTransformInv_apply]
    _ = ∫ x : E, (𝓕⁻ φ) x • v x := by
      have hf : (-innerₗ E).flip = -innerₗ E := by
        ext x y
        exact congrArg Neg.neg (real_inner_comm x y)
      have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := -innerₗ E) (μ := (volume : Measure E)) (ν := volume) Real.continuous_fourierChar
        (show Continuous (fun p : E × E => -inner ℝ p.1 p.2) by fun_prop) φ.integrable (L1.integrable_coeFn v)
      rw [hf] at h
      simp only [SchwartzMap.fourierInv_coe]
      convert h.symm using 1
    _ = _ := rfl
  rfl

/-- A tempered distribution lying in all integral Sobolev spaces has an actual
bounded smooth representative. All moments of a single L1 Fourier representative
are proved first, so the smooth representatives do not depend on the order. -/
theorem all_orders_smooth_representative {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolev n 2 u) :
    ∃ g : BoundedContinuousFunction E F, ContDiff ℝ (⊤ : ℕ∞) (g : E → F) ∧
      u = ((g.memLp_top.toLp _ : Lp F ∞ (volume : Measure E)) : 𝓢'(E,F)) := by
  obtain ⟨v,hv,hm⟩ := all_orders_fourier_moments hu
  refine ⟨Real.Lp.fourierTransformInv v,?_,?_⟩
  · have hs := Real.contDiff_fourier (N := (⊤ : ℕ∞)) (fun n _ => hm n)
    convert hs.comp contDiff_neg using 1
    ext x
    exact (Real.Lp.fourierTransformInv_apply v x).trans (Real.fourierInv_eq_fourier_neg _ _)
  · rw [l1_inverse_fourier_distribution,← hv,fourierInv_fourier_eq]

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Local Bessel-potential regularity, using actual compact smooth multipliers. -/
def LocalSobolev (Ω : Set E) (s : ℝ) (u : 𝓢'(E,F)) : Prop :=
  ∀ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Ω →
    MemSobolev s 2 (smulLeftCLM F g u)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma derivative_support_subset (g : E → ℂ) (m : E) :
    tsupport (fun x => fderiv ℝ g x m) ⊆ tsupport g :=
  (tsupport_comp_subset (g := fun T : E →L[ℝ] ℂ => T m) (by simp) (fderiv ℝ g)).trans
    (tsupport_fderiv_subset ℝ)

lemma LocalSobolev.mono {Ω : Set E} {s t : ℝ} {u : 𝓢'(E,F)}
    (h : LocalSobolev Ω s u) (hst : t ≤ s) : LocalSobolev Ω t u :=
  fun g hg hc hs => (h g hg hc hs).mono hst

lemma LocalSobolev.product_derivative {Ω : Set E} {s : ℝ} {u : 𝓢'(E,F)}
    (h : LocalSobolev Ω s u) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (m : E) :
    MemSobolev (s-1) 2 (smulLeftCLM F g (∂_{m} u)) := by
  have hdg := (compact_derivative hc m).hasTemperateGrowth (smooth_derivative hg m)
  have h1 := (h g hg hc hs).lineDerivOp (m := m)
  have h2 := h _ (smooth_derivative hg m) (compact_derivative hc m)
    ((derivative_support_subset g m).trans hs)
  have h3 := h1.sub (h2.mono (by linarith : s-1 ≤ s))
  rw [distribution_leibniz (hc.hasTemperateGrowth hg) m hdg,add_sub_cancel_left] at h3
  exact h3

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma laplacian_product {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (u : 𝓢'(E,F)) :
    Δ (smulLeftCLM F g u) = smulLeftCLM F g (Δ u)+
      ∑ d, (smulLeftCLM F (fun x => fderiv ℝ (fun y => fderiv ℝ g y (b d)) x (b d)) u+
        (2 : ℂ) • smulLeftCLM F (fun x => fderiv ℝ g x (b d)) (∂_{b d} u)) := by
  classical
  rw [laplacian_eq_sum b,laplacian_eq_sum b,map_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  have hgd := smooth_derivative hg (b d)
  have hcd := compact_derivative hc (b d)
  rw [distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd),LineDeriv.lineDerivOp_add,
    distribution_leibniz (hcd.hasTemperateGrowth hgd) _
      ((compact_derivative hcd (b d)).hasTemperateGrowth (smooth_derivative hgd (b d))),
    distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd)]
  module

/-- Local distributional equation with scalar Laplacian principal part. The
coefficients need only be globally smooth: cutoff multiplication, not a hidden
boundedness or temperedness condition, defines every coefficient product. -/
def LocalEllipticEquation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ω : Set E) (b : OrthonormalBasis ι ℝ E)
    (a : κ → κ → ι → E → ℂ) (c : κ → κ → E → ℂ) (f u : κ → 𝓢'(E,F)) : Prop :=
  ∀ i g, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Ω →
    smulLeftCLM F g (Δ (u i)) =
      (∑ j, ∑ d, smulLeftCLM F (g*a i j d) (∂_{b d} (u j)))+
      (∑ j, smulLeftCLM F (g*c i j) (u j))+smulLeftCLM F g (f i)

/-- One full local Sobolev order of elliptic gain, including the initial
L2-to-H1 step. This uses no regularity of the unknown beyond the stated order. -/
theorem local_elliptic_gain {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Ω : Set E} (b : OrthonormalBasis ι ℝ E)
    (a : κ → κ → ι → E → ℂ) (c : κ → κ → E → ℂ)
    (ha : ∀ i j d, ContDiff ℝ (⊤ : ℕ∞) (a i j d))
    (hc : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (c i j))
    {f u : κ → 𝓢'(E,F)} (heq : LocalEllipticEquation Ω b a c f u)
    {s : ℝ} (hu : ∀ i, LocalSobolev Ω s (u i))
    (hf : ∀ i, LocalSobolev Ω (s-1) (f i)) :
    ∀ i, LocalSobolev Ω (s+1) (u i) := by
  classical
  intro i g hg hgc hgs
  have hsource : MemSobolev (s-1) 2 (smulLeftCLM F g (Δ (u i))) := by
    rw [heq i g hg hgc hgs]
    refine ((sobolev_sum Finset.univ (fun j _ => sobolev_sum Finset.univ (fun d _ =>
      (hu j).product_derivative (hg.mul (ha i j d)) hgc.mul_right
        (tsupport_mul_subset_left.trans hgs) (b d)))).add ?_).add (hf i g hg hgc hgs)
    exact sobolev_sum Finset.univ (fun j _ =>
      (hu j _ (hg.mul (hc i j)) hgc.mul_right (tsupport_mul_subset_left.trans hgs)).mono (by linarith))
  have hΔ : MemSobolev (s-1) 2 (Δ (smulLeftCLM F g (u i))) := by
    rw [laplacian_product b hg hgc]
    apply hsource.add
    apply sobolev_sum Finset.univ
    intro d _
    have hgd := smooth_derivative hg (b d)
    have hcd := compact_derivative hgc (b d)
    have hsd := (derivative_support_subset g (b d)).trans hgs
    exact ((hu i _ (smooth_derivative hgd (b d)) (compact_derivative hcd (b d))
      ((derivative_support_subset _ (b d)).trans hsd)).mono (by linarith)).add
        (((hu i).product_derivative hgd hcd hsd (b d)).smul 2)
  have h := laplacian_gain ((hu i g hg hgc hgs).mono (by linarith : s-1 ≤ s)) hΔ
  convert h using 1
  ring

end ElasticityRegularity

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators
namespace ElasticityDistribution
open ElasticityAugmented TemperedDistribution
abbrev Test := 𝓢(X,ℂ)

/-- Equality of actual distributions tested strictly within the open domain. -/
def LocalEq (Ω : Set X) (u v : Dist) : Prop :=
  ∀ φ : Test, HasCompactSupport (φ : X → ℂ) → tsupport (φ : X → ℂ) ⊆ Ω → u φ=v φ
namespace LocalEq
variable {Ω : Set X} {u v w u' v' : Dist}
lemma refl (u : Dist) : LocalEq Ω u u := fun _ _ _ => rfl
lemma symm (h : LocalEq Ω u v) : LocalEq Ω v u := fun φ hc hs => (h φ hc hs).symm
lemma trans (h : LocalEq Ω u v) (h' : LocalEq Ω v w) : LocalEq Ω u w :=
  fun φ hc hs => (h φ hc hs).trans (h' φ hc hs)
lemma add (h : LocalEq Ω u v) (h' : LocalEq Ω u' v') : LocalEq Ω (u+u') (v+v') := by
  intro φ hc hs
  simp only [add_apply,h φ hc hs,h' φ hc hs]
lemma sub (h : LocalEq Ω u v) (h' : LocalEq Ω u' v') : LocalEq Ω (u-u') (v-v') := by
  intro φ hc hs
  simp only [sub_apply,h φ hc hs,h' φ hc hs]
lemma smul (h : LocalEq Ω u v) (c : ℂ) : LocalEq Ω (c • u) (c • v) := by
  intro φ hc hs
  simp only [smul_apply,h φ hc hs]
lemma sum {ι : Type*} (s : Finset ι) {a b : ι → Dist} (h : ∀ i ∈ s, LocalEq Ω (a i) (b i)) :
    LocalEq Ω (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  intro φ hc hs
  simp only [sum_apply]
  exact Finset.sum_congr rfl (fun i hi => h i hi φ hc hs)
lemma coeff (h : LocalEq Ω u v) (a : Coeff) : LocalEq Ω (a • u) (a • v) := by
  intro φ hc hs
  change u (SchwartzMap.smulLeftCLM ℂ (eval a) φ) = v (SchwartzMap.smulLeftCLM ℂ (eval a) φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (growth a),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_left : HasCompactSupport (eval a * (φ : X → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (growth a),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_right (f := eval a) (g := (φ : X → ℂ))).trans hs
lemma derivative (h : LocalEq Ω u v) (i : Fin 3) : LocalEq Ω (dd i u) (dd i v) := by
  intro φ hc hs
  change u (- ∂_{e i} φ) = v (- ∂_{e i} φ)
  apply h
  · change HasCompactSupport (fun x => -((∂_{e i} φ : Test) x))
    exact (hc.fderiv_apply (𝕜 := ℝ) (e i)).neg
  · change tsupport (-((∂_{e i} φ : Test) : X → ℂ)) ⊆ Ω
    rw [tsupport_neg]
    exact (ElasticityRegularity.derivative_support_subset (φ : X → ℂ) (e i)).trans hs
lemma cutoff (h : LocalEq Ω u v) {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) :
    smulLeftCLM ℂ g u = smulLeftCLM ℂ g v := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ g φ) = v (SchwartzMap.smulLeftCLM ℂ g φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_right : HasCompactSupport (g * (φ : X → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_left (f := g) (g := (φ : X → ℂ))).trans hs
end LocalEq

lemma LocalEq.shifted {Ω : Set X} {u v : Dist} (h : LocalEq Ω u v) (z : Fin 3 → ℂ) (i : Fin 3) :
    LocalEq Ω (sd z i u) (sd z i v) :=
  (h.derivative i).add (h.smul (z i))
lemma LocalEq.divergence {Ω : Set X} {u v : Fin 3 → Dist} (h : ∀ i, LocalEq Ω (u i) (v i))
    (z : Fin 3 → ℂ) : LocalEq Ω (divd z u) (divd z v) :=
  LocalEq.sum Finset.univ (fun i _ => (h i).shifted z i)

def normSource (z : Fin 3 → ℂ) (m n o : Coeff) (F : Fin 3 → Dist) : Fin 4 → Dist :=
  Fin.cons (o • (divd z F-(2 : ℂ) • (n • ∑ i, dc i m • F i))) (fun i => n • F i)

/-- The local physical stress-divergence equation implies the true normalized
augmented equation. The fourth component is the actual shifted divergence. -/
theorem local_normalized_system {Ω : Set X} (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (u F : Fin 3 → Dist) (h : ∀ i, LocalEq Ω (phys z lam m u i) (F i)) :
    ∀ i, LocalEq Ω (normPair z lam m n o u (divd z u) i) (normSource z m n o F i) := by
  have hr (i : Fin 3) : LocalEq Ω (rd z lam m u (divd z u) i) (F i) := by
    rw [← physical_expansion]
    exact h i
  have hs : LocalEq Ω (scd z lam m u (divd z u)) (divd z F) := by
    rw [← physical_divergence]
    exact LocalEq.divergence h z
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact (hs.sub (((LocalEq.sum Finset.univ (fun j _ => (hr j).coeff (dc j m))).coeff n).smul 2)).coeff o
  · exact (hr i).coeff n

lemma lapd_expand (z : Fin 3 → ℂ) (u : Dist) :
    lapd z u = Δ u + (∑ i, (2*z i) • dd i u)+(∑ i, z i*z i) • u := by
  have he (i : Fin 3) : sd z i (sd z i u)=dd i (dd i u)+(2*z i) • dd i u+(z i*z i) • u := by
    simp only [sd_apply,map_add,map_smul,smul_add,smul_smul]
    module
  rw [lapd]
  simp only [he,Finset.sum_add_distrib,← Finset.sum_smul]
  congr 2
  simpa only [dd_apply,e,EuclideanSpace.basisFun_apply] using
    (laplacian_eq_sum (EuclideanSpace.basisFun (Fin 3) ℝ) u).symm

end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma MemSobolev.local_zero {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) (Ω : Set E) :
    LocalSobolev Ω 0 u := by
  intro g hg hc _
  exact sobolev_zero_product (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) hu

theorem local_elliptic_all_orders {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Ω : Set E} (b : OrthonormalBasis ι ℝ E)
    (a : κ → κ → ι → E → ℂ) (c : κ → κ → E → ℂ)
    (ha : ∀ i j d, ContDiff ℝ (⊤ : ℕ∞) (a i j d))
    (hc : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (c i j))
    {f u : κ → 𝓢'(E,F)} (heq : LocalEllipticEquation Ω b a c f u)
    (hu : ∀ i, LocalSobolev Ω 0 (u i))
    (hf : ∀ n : ℕ, ∀ i, LocalSobolev Ω n (f i)) :
    ∀ n : ℕ, ∀ i, LocalSobolev Ω n (u i) := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero]; exact hu
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one]
    exact local_elliptic_gain b a c ha hc heq ih (fun i =>
      (hf n i).mono (by linarith : (n : ℝ)-1 ≤ n))

/-- The actual cutoff of an L2 weak solution is represented by one bounded
smooth function, simultaneously at all Sobolev orders. This is the distributional
interior-regularity conclusion used for physical correction and planar limits. -/
theorem local_elliptic_cutoff_smooth {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Ω : Set E} (b : OrthonormalBasis ι ℝ E)
    (a : κ → κ → ι → E → ℂ) (c : κ → κ → E → ℂ)
    (ha : ∀ i j d, ContDiff ℝ (⊤ : ℕ∞) (a i j d))
    (hc : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (c i j))
    {f u : κ → 𝓢'(E,F)} (heq : LocalEllipticEquation Ω b a c f u)
    (hu : ∀ i, LocalSobolev Ω 0 (u i))
    (hf : ∀ n : ℕ, ∀ i, LocalSobolev Ω n (f i))
    (i : κ) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ω) :
    ∃ v : BoundedContinuousFunction E F, ContDiff ℝ (⊤ : ℕ∞) (v : E → F) ∧
      smulLeftCLM F g (u i) = ((v.memLp_top.toLp _ : Lp F ∞ (volume : Measure E)) : 𝓢'(E,F)) := by
  exact all_orders_smooth_representative (fun n =>
    local_elliptic_all_orders b a c ha hc heq hu hf n i g hg hgc hgs)

end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
namespace ElasticityDistribution
open ElasticityAugmented ElasticityRegularity
namespace LocalSobolev
variable {Ω : Set X} {s t : ℝ} {u v : Dist}
lemma add (h : ElasticityRegularity.LocalSobolev Ω s u)
    (h' : ElasticityRegularity.LocalSobolev Ω s v) :
    ElasticityRegularity.LocalSobolev Ω s (u+v) := by
  intro g hg hc hs
  rw [map_add]
  exact (h g hg hc hs).add (h' g hg hc hs)
lemma sub (h : ElasticityRegularity.LocalSobolev Ω s u)
    (h' : ElasticityRegularity.LocalSobolev Ω s v) :
    ElasticityRegularity.LocalSobolev Ω s (u-v) := by
  intro g hg hc hs
  rw [map_sub]
  exact (h g hg hc hs).sub (h' g hg hc hs)
lemma smul (h : ElasticityRegularity.LocalSobolev Ω s u) (c : ℂ) :
    ElasticityRegularity.LocalSobolev Ω s (c • u) := by
  intro g hg hc hs
  rw [map_smul]
  exact (h g hg hc hs).smul c
lemma sum {ι : Type*} (S : Finset ι) {u : ι → Dist}
    (h : ∀ i ∈ S, ElasticityRegularity.LocalSobolev Ω s (u i)) :
    ElasticityRegularity.LocalSobolev Ω s (∑ i ∈ S, u i) := by
  intro g hg hc hs
  rw [map_sum]
  exact sobolev_sum S (fun i hi => h i hi g hg hc hs)
lemma coeff (h : ElasticityRegularity.LocalSobolev Ω s u) (a : Coeff) :
    ElasticityRegularity.LocalSobolev Ω s (a • u) := by
  intro g hg hc hs
  have := h (g*eval a) (hg.mul (eval_smooth a)) hc.mul_right (tsupport_mul_subset_left.trans hs)
  change MemSobolev s 2 (smulLeftCLM ℂ g (smulLeftCLM ℂ (eval a) u))
  rw [smulLeftCLM_smulLeftCLM_apply (growth a) (hc.hasTemperateGrowth hg),mul_comm]
  exact this
lemma derivative (h : ElasticityRegularity.LocalSobolev Ω s u) (i : Fin 3) :
    ElasticityRegularity.LocalSobolev Ω (s-1) (dd i u) := by
  intro g hg hc hs
  exact h.product_derivative hg hc hs (e i)
lemma shifted (h : ElasticityRegularity.LocalSobolev Ω s u) (z : Fin 3 → ℂ) (i : Fin 3) :
    ElasticityRegularity.LocalSobolev Ω (s-1) (sd z i u) :=
  add (derivative h i) (smul (h.mono (by linarith)) (z i))
lemma divergence {u : Fin 3 → Dist} (h : ∀ i, ElasticityRegularity.LocalSobolev Ω s (u i))
    (z : Fin 3 → ℂ) : ElasticityRegularity.LocalSobolev Ω (s-1) (divd z u) :=
  sum Finset.univ (fun i _ => shifted (h i) z i)
end LocalSobolev

lemma LocalEq.localSobolev {Ω : Set X} {s : ℝ} {u v : Dist} (h : LocalEq Ω u v)
    (hv : ElasticityRegularity.LocalSobolev Ω s v) : ElasticityRegularity.LocalSobolev Ω s u := by
  intro g hg hc hs
  rw [h.cutoff hg hc hs]
  exact hv g hg hc hs

/-- Local gain from an actual distributional Laplacian; includes negative order
starting points. The cutoff commutator is proved, not silently discarded. -/
theorem local_laplacian_gain {Ω : Set X} {s : ℝ} {u : Dist}
    (hu : ElasticityRegularity.LocalSobolev Ω s u)
    (hΔ : ElasticityRegularity.LocalSobolev Ω (s-1) (Δ u)) :
    ElasticityRegularity.LocalSobolev Ω (s+1) u := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  intro g hg hgc hgs
  have hb : MemSobolev (s-1) 2 (Δ (smulLeftCLM ℂ g u)) := by
    rw [laplacian_product b hg hgc]
    apply (hΔ g hg hgc hgs).add
    apply sobolev_sum Finset.univ
    intro d _
    have hgd := smooth_derivative hg (b d)
    have hcd := compact_derivative hgc (b d)
    have hsd := (derivative_support_subset g (b d)).trans hgs
    exact ((hu _ (smooth_derivative hgd (b d)) (compact_derivative hcd (b d))
      ((derivative_support_subset _ (b d)).trans hsd)).mono (by linarith)).add
        ((hu.product_derivative hgd hcd hsd (b d)).smul 2)
  have h := laplacian_gain ((hu g hg hgc hgs).mono (by linarith : s-1 ≤ s)) hb
  convert h using 1
  ring

lemma normSource_local {Ω : Set X} {s : ℝ} (z : Fin 3 → ℂ) (m n o : Coeff)
    (F : Fin 3 → Dist) (hF : ∀ i, ElasticityRegularity.LocalSobolev Ω s (F i)) :
    ∀ i, ElasticityRegularity.LocalSobolev Ω (s-1) (normSource z m n o F i) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact LocalSobolev.coeff (LocalSobolev.sub (LocalSobolev.divergence hF z)
      (LocalSobolev.smul (LocalSobolev.coeff (LocalSobolev.sum Finset.univ (fun i _ =>
        LocalSobolev.coeff ((hF i).mono (by linarith)) (dc i m))) n) 2)) o
  · exact LocalSobolev.coeff ((hF i).mono (by linarith)) n

/-- Interior elliptic gain for the genuine normalized physical distribution
system, with no solution-regularity premise hidden in the equation. -/
theorem normalized_local_gain {Ω : Set X} {s : ℝ} (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (hn : n*m=1) (ho : o*(lam+m+m)=1) (U F : Fin 4 → Dist)
    (heq : ∀ i, LocalEq Ω (normPair z lam m n o (fun j => U j.succ) (U 0) i) (F i))
    (hU : ∀ i, ElasticityRegularity.LocalSobolev Ω s (U i))
    (hF : ∀ i, ElasticityRegularity.LocalSobolev Ω (s-1) (F i)) :
    ∀ i, ElasticityRegularity.LocalSobolev Ω (s+1) (U i) := by
  intro i
  let l₁ : Dist := ∑ k, ∑ j, coeffA (A := Coeff) dc lam m n o k i j • sd z k (U j)
  let l₀ : Dist := ∑ j, coeffV (A := Coeff) dc lam m n o i j • U j
  have h₁ : ElasticityRegularity.LocalSobolev Ω (s-1) l₁ := by
    apply LocalSobolev.sum
    intro k _
    apply LocalSobolev.sum
    intro j _
    exact LocalSobolev.coeff (LocalSobolev.shifted (hU j) z k) _
  have h₀ : ElasticityRegularity.LocalSobolev Ω (s-1) l₀ := by
    apply LocalSobolev.sum
    intro j _
    exact LocalSobolev.coeff ((hU j).mono (by linarith)) _
  have he : LocalEq Ω (lapd z (U i)) (F i-l₁-l₀) := by
    intro φ hc hs
    have hh := heq i φ hc hs
    rw [normalized_matrix z lam m n o hn ho] at hh
    change ((lapd z (U i)+l₁+l₀) : Dist) φ=(F i) φ at hh
    simp only [add_apply,sub_apply] at hh ⊢
    linear_combination hh
  have hlap := he.localSobolev (LocalSobolev.sub (LocalSobolev.sub (hF i) h₁) h₀)
  have hd : ElasticityRegularity.LocalSobolev Ω (s-1) (∑ k, (2*z k) • dd k (U i)) :=
    LocalSobolev.sum Finset.univ (fun k _ => LocalSobolev.smul
      (LocalSobolev.derivative (hU i) k) (2*z k))
  have hz : ElasticityRegularity.LocalSobolev Ω (s-1) ((∑ k, z k*z k) • U i) :=
    LocalSobolev.smul ((hU i).mono (by linarith)) _
  apply local_laplacian_gain (hU i)
  have hΔ := LocalSobolev.sub (LocalSobolev.sub hlap hz) hd
  simpa only [lapd_expand,add_sub_cancel_right] using hΔ

/-- All local Sobolev orders for an L2 physical solution with smooth source.
The physical fourth unknown is the actual shifted divergence, initially H^-1,
not an independent L2 unknown postulated as a hypothesis. -/
theorem physical_local_all_orders {Ω : Set X} (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (hn : n*m=1) (ho : o*(lam+m+m)=1) (u F : Fin 3 → Dist)
    (heq : ∀ i, LocalEq Ω (phys z lam m u i) (F i))
    (hu : ∀ i, ElasticityRegularity.LocalSobolev Ω 0 (u i))
    (hf : ∀ N : ℕ, ∀ i, ElasticityRegularity.LocalSobolev Ω N (F i)) :
    ∀ N : ℕ, ∀ i, ElasticityRegularity.LocalSobolev Ω N ((Fin.cons (divd z u) u : Fin 4 → Dist) i) := by
  let U : Fin 4 → Dist := Fin.cons (divd z u) u
  let FF := normSource z m n o F
  have hsys : ∀ i, LocalEq Ω (normPair z lam m n o (fun j => U j.succ) (U 0) i) (FF i) :=
    local_normalized_system z lam m n o u F heq
  have hm : ∀ i, ElasticityRegularity.LocalSobolev Ω (-1) (U i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · change ElasticityRegularity.LocalSobolev Ω (-1) (divd z u)
      simpa only [zero_sub] using LocalSobolev.divergence hu z
    · exact (hu i).mono (by norm_num)
  have hzero : ∀ i, ElasticityRegularity.LocalSobolev Ω 0 (U i) := by
    have hh := normalized_local_gain (s := -1) z lam m n o hn ho U FF hsys hm
      (fun i => (normSource_local z m n o F (hf 0) i).mono (by norm_num))
    simpa only [neg_add_cancel] using hh
  intro N
  induction N with
  | zero => rw [Nat.cast_zero]; exact hzero
  | succ N hN =>
    rw [Nat.cast_add,Nat.cast_one]
    exact normalized_local_gain z lam m n o hn ho U FF hsys hN
      (normSource_local z m n o F (hf N))

/-- Every compact cutoff of the actual augmented physical unknown has a single
bounded smooth representative. This is a conclusion, not an assumed classical
regularity theorem. -/
theorem physical_cutoff_smooth {Ω : Set X} (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (hn : n*m=1) (ho : o*(lam+m+m)=1) (u F : Fin 3 → Dist)
    (heq : ∀ i, LocalEq Ω (phys z lam m u i) (F i))
    (hu : ∀ i, ElasticityRegularity.LocalSobolev Ω 0 (u i))
    (hf : ∀ N : ℕ, ∀ i, ElasticityRegularity.LocalSobolev Ω N (F i))
    (i : Fin 4) {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ω) :
    ∃ v : BoundedContinuousFunction X ℂ, ContDiff ℝ (⊤ : ℕ∞) (v : X → ℂ) ∧
      smulLeftCLM ℂ g ((Fin.cons (divd z u) u : Fin 4 → Dist) i) =
        ((v.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure X)) : Dist) := by
  exact all_orders_smooth_representative (fun N =>
    physical_local_all_orders z lam m n o hn ho u F heq hu hf N i g hg hgc hgs)
end ElasticityDistribution

end

end OAI
