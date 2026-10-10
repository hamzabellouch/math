import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeReduction

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem exists_source_cube_bins (e B : ℝ) (he : 0<e) (hB : 2<B)
    (n : ℕ) (hn : 0<n) (hwidth : (49/100:ℝ)≤n*e)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) (ψ : FreeRow→ι→Character) :
    ∃idx grid : FreeRow→ℕ,∀u : FreeRow,
      1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
      let a : ℝ := 51/100+e*grid u
      let H : ℝ := (3*idx u+1:ℕ)*B
      (51/100:ℝ)≤a ∧ a≤1 ∧ B≤H ∧ H+B/2≤(3*idx u+2:ℕ)*B ∧
      a≤detectorMaximum (sourceDetectorFamily S hS η u (ψ u)) (3*idx u*B) ∧
      detectorMaximum (sourceDetectorFamily S hS η u (ψ u)) (3*idx u*B)<a+e ∧
      detectorMaximum (sourceDetectorFamily S hS η u (ψ u)) (3*(idx u+1:ℕ)*B)<a+2*e ∧
      (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS η u (ψ u) j) s=0 ∧
        ¬((sourceDetectorFamily S hS η u (ψ u) j).residue=1 ∧ s=1) ∧
        a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*B) := by
  have hex (u : FreeRow) := exists_detector_buffered_bin (sourceDetectorFamily S hS η u (ψ u)) B e hB he n hn hwidth
  choose idx grid hspec using hex
  refine ⟨idx,grid,?_⟩
  intro u
  rcases hspec u with ⟨hi,hin,ha,hlo,hhi,hnext,hzero,hdisk⟩
  refine ⟨hi,hin,?_,?_,ha,?_,?_,hlo,hhi,hnext,hzero⟩
  · apply Nat.le_floor
    apply (le_div_iff₀ he).mpr
    nlinarith
  · nlinarith [Nat.cast_nonneg (α:=ℝ) (grid u)]
  · push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) (idx u)]
  · push_cast
    linarith

theorem exists_source_cube_bin_number (e : ℝ) (he : 0<e) :
    ∃n : ℕ,0<n ∧ (49/100:ℝ)≤n*e := by
  refine ⟨⌈(49/100:ℝ)/e⌉₊+1,by omega,?_⟩
  have hh := Nat.le_ceil ((49/100:ℝ)/e)
  have hmul := (div_le_iff₀ he).mp hh
  push_cast
  nlinarith

theorem source_cube_height_eventually (τ : ℝ) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ 2<Z^τ := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hZ hpow
  exact ⟨hZ,hpow⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
