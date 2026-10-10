import OAI.NumberTheory.DirichletL.Detector.RaySlots
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRayNormalization
open HeckeFamily ProbePhysical ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

theorem log_power_absorption (c ell d : ℝ) (hc : 0<c) (hell : 0<ell) (hd : 0<d) :
    ∀ᶠZ : ℝ in atTop,Z^(ell/6-d)≤c*(Z^ell)^(1/6:ℝ)/Real.log (Z^ell) := by
  have hh := (isLittleO_log_rpow_atTop hd).bound (div_pos hc hell)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  have hZ0 : 0<Z := by linarith
  have hlog : 0<Real.log Z := Real.log_pos hZ1
  have hzd : 0<Z^d := Real.rpow_pos_of_pos hZ0 _
  have hb : ell*Real.log Z≤c*Z^d := by
    have hb' : Real.log Z≤(c/ell)*Z^d := by
      simpa only [Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos hzd] using hZ
    calc
      _ ≤ ell*((c/ell)*Z^d) := mul_le_mul_of_nonneg_left hb' hell.le
      _ = _ := by field_simp
  rw [Real.log_rpow hZ0,←Real.rpow_mul hZ0.le]
  apply (le_div_iff₀ (mul_pos hell hlog)).mpr
  calc
    Z^(ell/6-d)*(ell*Real.log Z) ≤ Z^(ell/6-d)*(c*Z^d) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hZ0.le _)
    _ = c*Z^(ell*(1/6:ℝ)) := by
      rw [mul_left_comm,←Real.rpow_add hZ0]
      congr 1
      ring_nf

theorem principalScalar_inverse_of_slot_bounds {ι : Type*} (J : Finset ι)
    (ell mass : ι→ℝ) (Z d eps : ℝ) (hZ : 1≤Z) (_hd : 0≤d)
    (hbudget : d*J.card≤eps) (hm : ∀i∈J,Z^(ell i/6-d)≤mass i) :
    |(Probe.principalScalar J Z (∑i∈J,ell i) mass)⁻¹|≤Z^eps := by
  have hZ0 : 0<Z := by linarith
  have hm0 : ∀i∈J,0≤mass i := fun i hi=>(Real.rpow_nonneg hZ0.le _).trans (hm i hi)
  have hprod : Z^(∑i∈J,(ell i/6-d))≤∏i∈J,mass i := by
    rw [Real.rpow_sum_of_pos hZ0]
    exact Finset.prod_le_prod₀ (fun i _=>Real.rpow_nonneg hZ0.le _) hm
  have hn : |Probe.principalScalar J Z (∑i∈J,ell i) mass|=
      Z^(-(∑i∈J,ell i)/6)*(∏i∈J,mass i) := by
    unfold Probe.principalScalar
    rw [abs_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_pos (Real.rpow_pos_of_pos hZ0 _),abs_of_nonneg (Finset.prod_nonneg hm0)]
  have hpow : Z^(-(∑i∈J,ell i)/6)*Z^(∑i∈J,(ell i/6-d))=Z^(-d*J.card) := by
    rw [←Real.rpow_add hZ0]
    congr 1
    rw [Finset.sum_sub_distrib,←Finset.sum_div,Finset.sum_const,nsmul_eq_mul]
    ring
  have hl : Z^(-eps)≤|Probe.principalScalar J Z (∑i∈J,ell i) mass| := by
    calc
      _ ≤ Z^(-d*J.card) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
      _ = Z^(-(∑i∈J,ell i)/6)*Z^(∑i∈J,(ell i/6-d)) := hpow.symm
      _ ≤ _ := by rw [hn];exact mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hZ0.le _)
  rw [abs_inv]
  have hi := (inv_le_inv₀ ((Real.rpow_pos_of_pos hZ0 (-eps)).trans_le hl)
    (Real.rpow_pos_of_pos hZ0 (-eps))).mpr hl
  simpa only [Real.rpow_neg hZ0.le,inv_inv] using hi

variable (M : Id) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hH

theorem ray_slot_subpower_lower (S : Finset Id) (W : ℝ→ℝ)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hsupp : Function.support W⊆Set.Ioo a b)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤W y) (hWne : W≠0) (ell d : ℝ) (hell : 0<ell) (hd : 0<d) :
    ∀ᶠZ : ℝ in atTop,Z^(ell/6-d)≤
      ∑P∈pool (RayQuotient.identityClass M H) S a b (Z^ell),
        W ((Ideal.absNorm P.val:ℝ)/(Z^ell))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
  obtain ⟨c,hc0,hbound⟩ := ray_pool_mass_eventually_lower_bound M H hH S W a b ha hab hsupp hW hc hp hW0 hWne
  filter_upwards [(tendsto_rpow_atTop hell).eventually hbound,log_power_absorption c ell d hc0 hell hd]
    with Z hZ hlog
  exact hlog.trans hZ

theorem ray_principalScalar_inverse_subpower {ι : Type*} (J : Finset ι)
    (S : Finset Id) (W : ι→ℝ→ℝ) (a b ell : ι→ℝ)
    (ha : ∀i∈J,0<a i) (hab : ∀i∈J,a i≤b i)
    (hsupp : ∀i∈J,Function.support (W i)⊆Set.Ioo (a i) (b i))
    (hW : ∀i∈J,ContDiff ℝ ∞ (W i)) (hc : ∀i∈J,HasCompactSupport (W i))
    (hp : ∀i∈J,tsupport (W i)⊆Set.Ioi 0)
    (hW0 : ∀i∈J,∀y,0≤W i y) (hWne : ∀i∈J,W i≠0) (hell : ∀i∈J,0<ell i)
    (eps : ℝ) (heps : 0<eps) :
    ∀ᶠZ : ℝ in atTop,
      |(Probe.principalScalar J Z (∑i∈J,ell i) (fun i=>
        ∑P∈pool (RayQuotient.identityClass M H) S (a i) (b i) (Z^(ell i)),
          W i ((Ideal.absNorm P.val:ℝ)/(Z^(ell i)))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ))))⁻¹|≤Z^eps := by
  let d : ℝ := eps/(J.card+1)
  have hd : 0<d := div_pos heps (by positivity)
  have hb : d*J.card≤eps := by
    dsimp [d]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0:ℝ)<J.card+1)]
    nlinarith
  have hm : ∀ᶠZ : ℝ in atTop,∀i∈J,Z^(ell i/6-d)≤
      ∑P∈pool (RayQuotient.identityClass M H) S (a i) (b i) (Z^(ell i)),
        W i ((Ideal.absNorm P.val:ℝ)/(Z^(ell i)))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
    apply (Filter.eventually_all_finset J).mpr
    intro i hi
    exact ray_slot_subpower_lower M H hH S (W i) (a i) (b i) (ha i hi) (hab i hi)
      (hsupp i hi) (hW i hi) (hc i hi) (hp i hi) (hW0 i hi) (hWne i hi) (ell i) d (hell i hi) hd
  filter_upwards [hm,eventually_ge_atTop (1:ℝ)] with Z hmass hZ
  exact principalScalar_inverse_of_slot_bounds J ell _ Z d eps hZ hd.le hb hmass

end SevenEighths.ProbeRayNormalization
end

end OAI
