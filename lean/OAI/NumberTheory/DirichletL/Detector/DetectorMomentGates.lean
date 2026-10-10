import OAI.NumberTheory.DirichletL.Detector.DetectorMomentData
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawFiberSource
import OAI.NumberTheory.DirichletL.Hecke.DetectorBatch
import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedElement

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open CanonicalCoefficientClass InverseInitialExcludedPeriod CanonicalQuadraticSieve
open InverseInitialRayAttachment CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

def sourceMomentPeriod (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):ℕ:=
  ∏j:Sum Bool (RayQuotient.Characters M H),
    (baseCharacter (sourceMomentData M H hH S hS η j)).period

def sourceMomentConductorBound (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):ℝ:=
  1+∑j:Sum Bool (RayQuotient.Characters M H),
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)

theorem sourceMomentPeriod_ne_zero (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    sourceMomentPeriod M H hH S hS η≠0:=by
  exact Finset.prod_ne_zero_iff.mpr (fun j _=>Nat.ne_of_gt (Character.period_pos _))

theorem sourceMomentPeriod_le (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    (j:Sum Bool (RayQuotient.Characters M H)):
    Ideal.span {(sourceMomentPeriod M H hH S hS η:O)}≤
      (baseCharacter (sourceMomentData M H hH S hS η j)).modulus:=by
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  have hd:(baseCharacter (sourceMomentData M H hH S hS η j)).period∣
      sourceMomentPeriod M H hH S hS η:=Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  obtain ⟨n,hn⟩:=hd
  rw [hn,Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Character.period_mem _)

theorem sourceMomentConductorBound_pos (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    0<sourceMomentConductorBound M H hH S hS η:=by
  unfold sourceMomentConductorBound
  positivity

theorem sourceMomentConductor_le (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    (j:Sum Bool (RayQuotient.Characters M H)):
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
      sourceMomentConductorBound M H hH S hS η:=by
  have hh:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Sum Bool (RayQuotient.Characters M H))))=>
    (Nat.cast_nonneg (α:=ℝ) (baseCharacter (sourceMomentData M H hH S hS η k)).modulus.absNorm))
      (Finset.mem_univ j)
  unfold sourceMomentConductorBound
  linarith

theorem sourceMoment_deleted_base_gates (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    let q:=sourceMomentPeriod M H hH S hS η
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    ∀j:Sum Bool (RayQuotient.Characters M H),
      let χ:=(baseCharacter (sourceMomentData M H hH S hS η j)).excludePrimes
        (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
      (∀x,‖elementCharacter (idealCoeff χ).toMonoidHom x‖≤1) ∧
      FactorsModulo (fixedBaseConductor (deletedPeriod q))
        (elementCharacter (idealCoeff χ).toMonoidHom):=by
  dsimp only
  let q:=sourceMomentPeriod M H hH S hS η
  have hq:q≠0:=sourceMomentPeriod_ne_zero M H hH S hS η
  refine ⟨deletedPeriod_ne_zero q hq,deleted_excluded_eq q hq,?_⟩
  intro j
  exact (deleted_physical_base_gates _ q hq (sourceMomentPeriod_le M H hH S hS η j)).2.2

theorem sourceMoment_large_eventually (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    {Slot:Type*}[Fintype Slot](ell:Slot→ℝ)(hell:∀s,0<ell s):
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→
      ∀j:Sum Bool (RayQuotient.Characters M H),∀s:Slot,
        ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
          (Z^d)^(ell s/d):=by
  have ht:∀ᶠZ:ℝ in atTop,∀s:Slot,sourceMomentConductorBound M H hH S hS η<Z^(ell s):=by
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0≤Z),mul_div_cancel₀ _ hd.ne']
  exact (sourceMomentConductor_le M H hH S hS η j).trans (ht s)

end SevenEighths.ProbeHighRowFamily

end

end OAI
