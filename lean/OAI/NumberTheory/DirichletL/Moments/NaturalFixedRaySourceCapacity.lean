import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceBatch

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeScale HeckeInverseAmplification
open CenteredMomentNaturalRowSource CenteredMomentDetectorDictionary
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sectorConductorFactor (η₀ : Character) : ℕ :=
  η₀.modulus.absNorm*fixedConductorFactor*(M.absNorm*η₀.modulus.absNorm)

lemma initial_sector_modulus (η₀ : Character) (u : FreeRow) (θ : RayQuotient.Characters M H) :
    ((naturalRow η₀ u.val u.property.1).character.product (relativeCharacter M H hH η₀ θ)).modulus.absNorm≤
      sectorConductorFactor M η₀*(Ideal.span {u.val}).absNorm := by
  have hn:=(naturalRow η₀ u.val u.property.1).natural_modulus_bound
  have hs:=relativeCharacter_modulus M H hH η₀ θ
  apply (product_modulus_bound _ _).trans
  apply (Nat.mul_le_mul hn hs).trans_eq
  unfold sectorConductorFactor
  ring

theorem eventually_source_sector_capacity
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (margin : ℝ) (hmargin : 0<margin) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters M H),∀d : ℝ,∀u : FreeRow,
      ((Ideal.span {u.val}).absNorm:ℝ)≤Z^(d-margin)→
      ∀θ : RayQuotient.Characters M H,
      (((naturalRow (sourceMomentBase M H hH S hS η label) u.val u.property.1).character.product
        (relativeCharacter M H hH (sourceMomentBase M H hH S hS η label) θ)).modulus.absNorm:ℝ)≤Z^d := by
  have hc : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters M H),
      (sectorConductorFactor M (sourceMomentBase M H hH S hS η label):ℝ)≤Z^margin := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (0:ℝ)] with Z hz hZ
  intro label d u hu θ
  have hb : (((naturalRow (sourceMomentBase M H hH S hS η label) u.val u.property.1).character.product
      (relativeCharacter M H hH (sourceMomentBase M H hH S hS η label) θ)).modulus.absNorm:ℝ)≤
      (sectorConductorFactor M (sourceMomentBase M H hH S hS η label):ℝ)*((Ideal.span {u.val}).absNorm:ℝ) := by
    exact_mod_cast initial_sector_modulus M H hH (sourceMomentBase M H hH S hS η label) u θ
  apply hb.trans
  calc
    _≤Z^margin*Z^(d-margin) := mul_le_mul (hz label) hu (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _=Z^d := by rw [←Real.rpow_add hZ]; congr 1; ring

theorem sourceData_fiber_sector_capacity {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀d a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : HeckeDetectorBatch.Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i,
      (∀u∈B.rows,ProbeHighRowFamily.rowNorm u≤Z^(d-D.t))→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀u∈(B.fiber bin label J K hne).rows,∀θ : RayQuotient.Characters F.modulus ⊤,
      (((naturalRow (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label)
        u.val u.property.1).character.product
        (relativeCharacter F.modulus ⊤ le_top
          (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) θ)).modulus.absNorm:ℝ)≤Z^d := by
  filter_upwards [eventually_source_sector_capacity F.modulus ⊤ le_top
    F.S F.exclusions.prime η D.t D.t_pos] with Z hz
  intro d a ε tstar T allowance i B hcap bin label J K hne u hu θ
  apply hz label d u ?_ θ
  simp only [HeckeDetectorBatch.Batch.fiber, HeckeDetectorFiberPartition.toFiber,
    HeckeDetectorFiberPartition.fiber, Finset.mem_filter] at hu
  have hmem : u∈B.rows := hu.1
  exact hcap u hmem

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
