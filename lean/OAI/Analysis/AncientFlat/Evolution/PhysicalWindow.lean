import OAI.Analysis.AncientFlat.Evolution.PhysicalCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma physical_apply (γ : ℝ) (v : ℝ → C₀(V,ℂ)) (t : ℝ) (x : V) :
    physical γ v t x=(Real.exp ((1/2-γ)*similarityTime t) : ℂ)*
      v (similarityTime t) (Real.exp (similarityTime t/4) • x) := by
  simp [physical,dil_apply]
lemma similarityTime_exp {t : ℝ} (ht : t<0) : Real.exp (similarityTime t)=(-t)⁻¹ := by
  rw [similarityTime,Real.exp_neg,Real.exp_log (neg_pos.mpr ht)]
lemma similarityTime_deriv {t : ℝ} (ht : t<0) :
    HasDerivAt similarityTime (Real.exp (similarityTime t)) t := by
  have hh := ((hasDerivAt_id t).neg.log (ne_of_gt (neg_pos.mpr ht))).neg
  convert hh using 1 <;> first | rfl | (rw [similarityTime_exp ht]; simp only [Pi.neg_apply,id_eq,neg_div_neg_eq,neg_inv,one_div])
lemma physical_contDiff (γ : ℝ) (v : ℝ → C₀(V,ℂ))
    (hv : ∀ t, ContDiff ℝ 4 (fun x => v t x)) (t : ℝ) :
    ContDiff ℝ 4 (fun x => physical γ v t x) := by
  have hc := (hv (similarityTime t)).comp
    (show ContDiff ℝ 4 (fun x : V => Real.exp (similarityTime t/4) • x) from contDiff_const.smul contDiff_id)
  simpa only [physical_apply,smul_eq_mul,Function.comp_apply] using hc.const_smul (Real.exp ((1/2-γ)*similarityTime t) : ℂ)

def physicalWindow (γ a : ℝ) (u : ℝ → C₀(V,ℂ)) (s : ℝ) : C₀(V,ℂ) :=
  (Real.exp ((1/2-γ)*a+s/2) : ℂ) • dil (-a) (u s)
lemma physicalWindow_apply (γ a : ℝ) (u : ℝ → C₀(V,ℂ)) (s : ℝ) (x : V) :
    physicalWindow γ a u s x=(Real.exp ((1/2-γ)*a+s/2) : ℂ)*u s (Real.exp (a/4) • x) := by
  simp [physicalWindow,dil_apply]
lemma physical_eq_window (γ a : ℝ) (u v : ℝ → C₀(V,ℂ)) (t : ℝ)
    (he : renormalized γ u (similarityTime t-a)=v (similarityTime t)) :
    physical γ v t=physicalWindow γ a u (similarityTime t-a) := by
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rw [physical_apply,←he]
  change (Real.exp ((1/2-γ)*similarityTime t) : ℂ)*
    ((Real.exp (γ*(similarityTime t-a)) : ℂ)*
      u (similarityTime t-a) (Real.exp (-(similarityTime t-a)/4) • (Real.exp (similarityTime t/4) • x)))=_
  rw [smul_smul,←Real.exp_add,show -(similarityTime t-a)/4+similarityTime t/4=a/4 by ring]
  rw [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,physicalWindow_apply]
  congr 2
  ring_nf
variable [FiniteDimensional ℝ V]
lemma MovesWithSource.physicalWindow_deriv {Af Bf : V → ℝ} {f : ℝ →ᵇ C₀(V,ℂ)}
    {d : C₀(V,ℂ)} {u : ℝ → C₀(V,ℂ)} (hu : MovesWithSource Af Bf f d u)
    (γ a : ℝ) {s : ℝ} (hs : s∈Ioo (0:ℝ) 1) (x : V) :
    HasDerivAt (fun r => physicalWindow γ a u r x)
      ((Real.exp ((1/2-γ)*a+s/2) : ℂ)*f s (Real.exp ((a+s)/4) • x)-
        (Real.exp (-(a+s))/16*Af (Real.exp ((a+s)/4) • x) : ℝ) •
          Δ (Δ (fun y => physicalWindow γ a u s y)) x-
        (Bf (Real.exp ((a+s)/4) • x) : ℝ) • physicalWindow γ a u s x) s := by
  obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 s hs
  have he := (BoundedContinuousFunction.evalCLM ℝ (Real.exp (a/4) • x)).hasFDerivAt.comp_hasDerivAt s hp
  have hv := (((hasDerivAt_id s).div_const 2).const_add ((1/2-γ)*a)).exp.ofReal_comp
  have hh := hv.mul he
  have hfun : (fun r => physicalWindow γ a u r x)=
      (fun r => (Real.exp ((1/2-γ)*a+r/2) : ℂ)*u r (Real.exp (a/4) • x)) :=
    funext (fun r => physicalWindow_apply γ a u r x)
  rw [hfun]
  convert hh using 1 <;> try rfl
  simp only [Function.comp_apply,BoundedContinuousFunction.evalCLM_apply,ZeroAtInftyContinuousMap.toBCF_apply,id_eq]
  rw [hpe]
  have hsum : Real.exp (s/4) • Real.exp (a/4) • x=Real.exp ((a+s)/4) • x := by
    rw [smul_smul,←Real.exp_add]; congr 2; ring
  rw [hsum]
  have hc : ContDiff ℝ 4 (fun y => u s (Real.exp (a/4) • y)) :=
    (hu.2.2.1 s hs).comp (contDiff_const.smul contDiff_id)
  have hbilap : Δ (Δ (fun y => physicalWindow γ a u s y)) x=
      (Real.exp ((1/2-γ)*a+s/2) : ℂ)*((Real.exp a : ℝ) • Δ (Δ (fun y => u s y)) (Real.exp (a/4) • x)) := by
    simp only [physicalWindow_apply,←smul_eq_mul]
    rw [bilaplacian_smul hc]
    dsimp only
    rw [bilaplacian_scale _ _ (hu.2.2.1 s hs)]
    have hexp : Real.exp (a/4)^4=Real.exp a := by
      rw [←Real.exp_nat_mul]; congr 1; ring
    rw [hexp]
  rw [hbilap,physicalWindow_apply]
  have hcancel : Real.exp (-(a+s))*Real.exp a=Real.exp (-s) := by
    rw [←Real.exp_add]; congr 1; ring
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,
    Complex.ofReal_one]
  have hc' := congrArg Complex.ofReal hcancel
  simp only [Complex.ofReal_mul] at hc'
  linear_combination (-(Real.exp ((1/2-γ)*a+s/2) : ℂ)/16*
    (Af (Real.exp ((a+s)/4) • x) : ℂ)*Δ (Δ (fun y => u s y)) (Real.exp (a/4) • x))*hc'
end FlatSimilarity

end

end OAI
