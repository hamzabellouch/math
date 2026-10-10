import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentDetectorDictionary
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open ProbeHighRowFamily HeckeDetectorDyadicProfiles CenteredMomentPrimeSlot HeckeDetectorRowwisePolynomial
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem eventually_source_batch_plain_sectors {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (hM : M=∏P∈S,P)
    (η : Character) (ell : Fin N→ℝ) (hell : ∀s,0<ell s)
    (W : Fin N→ℝ→ℂ) (hW : ∀s,Function.support (W s)⊆Set.Ici 1) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≠0→∀a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N) (Z^d) a ε tstar T allowance i,
      B.data=sourceMomentData M H hH S hS η→B.widths=(fun s=>ell s/d)→B.profile=W→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin N),∀j k : ℕ,∀σ t : ℝ,
      let F:=B.fiber bin label J K hne
      let η₀:=sourceMomentBase M H hH S hS η label
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) ((Z^d)^F.m) σ t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) ((Z^d)^F.m) σ t*
          F.physicalProduct selected u‖^2)≤
        ∑θ : selected→RayQuotient.Characters M H,‖averageWeight (ι:=selected) M H‖*
          ∑u∈F.rows,‖fiberSector hH F η₀ selected j k σ t θ u‖^2 := by
  have hMm : M≤Ideal.span {rowMaskElement} := by
    rw [hM]
    exact source_product_le_rowMask S hbad
  filter_upwards [eventually_source_slots_coprime M H hH S hS η ell hell 1 (by norm_num),
    eventually_gt_atTop (0:ℝ)] with Z hz hZ
  intro d hd a ε tstar T allowance i B hdata hwidth hprofile bin label J K hne selected j k σ t
  dsimp only
  convert fiber_plain_sector_energy hH (B.fiber bin label J K hne)
    (sourceMomentBase M H hH S hS η label) ?_ hMm (Real.rpow_pos_of_pos hZ _) selected j k σ t ?_ using 1
  · congr 2 ; apply Subsingleton.elim
  · change B.data label=momentData (sourceMomentBase M H hH S hS η label)
    rw [hdata,sourceMomentData_base]
  · intro s hs P hP hp
    change P∈primePool M H (B.upper s) ((Z^d)^(B.widths s)) at hP
    change B.profile s ((P.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hp
    rw [hwidth] at hP
    rw [hwidth,hprofile] at hp
    exact hz label s d hd (W s) (B.upper s) (hW s) P hP hp

theorem sourceData_batch_gate {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≠0→∀a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i,
      B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η→
      B.widths=(fun s=>D.ell s/d)→B.profile=(fun _ y=>(F.w y:ℂ))→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin D.N),∀j k : ℕ,∀σ t : ℝ,
      let Bf:=B.fiber bin label J K hne
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      (∑u∈Bf.rows,‖polynomial (Bf.family u Bf.label) false ((logProfile^[j]) positiveAnnular) ((Z^d)^Bf.m) σ t*
        polynomial (Bf.family u Bf.label) false ((logProfile^[k]) positiveAnnular) ((Z^d)^Bf.m) σ t*
          Bf.physicalProduct selected u‖^2)≤
        ∑θ : selected→RayQuotient.Characters F.modulus ⊤,‖averageWeight (ι:=selected) F.modulus ⊤‖*
          ∑u∈Bf.rows,‖fiberSector le_top Bf η₀ selected j k σ t θ u‖^2 := by
  apply eventually_source_batch_plain_sectors F.modulus ⊤ le_top F.S F.exclusions.prime
    F.exclusions.bad rfl η D.ell (fun s=>(D.slots_bounds s).1) (fun _ y=>(F.w y:ℂ))
  intro s y hy
  have hn : F.w y≠0 := by
    intro h
    apply hy
    simp only [h,Complex.ofReal_zero]
  exact (F.support hn).1.le

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
