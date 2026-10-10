import OAI.NumberTheory.Jacobsthal.Primes.PrimeMarginalRecursion

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceParentBin

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport PrimeGridGeometry PrimeGridKernel
open PrimeMarginalRecursion DerivativeWeights

noncomputable def index (m : ℕ) (start : Node) : ℕ := ⌊start.ratio*(m:ℝ)⌋₊
noncomputable def initialConstant : ℝ := 1/phiEven (23/10)

theorem initialConstant_pos : 0 < initialConstant := by
  apply one_div_pos.mpr
  exact phiEven_pos (by norm_num)

theorem source_cell {m : ℕ} (hm : 1 ≤ m) (start : Node) (hs : 0 ≤ start.ratio) :
    start.ratio ∈ Ico (point m (index m start)) (point m (index m start+1)) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlo := Nat.floor_le (mul_nonneg hs hm0.le)
  have hhi := Nat.lt_floor_add_one (start.ratio*(m:ℝ))
  constructor
  · exact (div_le_iff₀ hm0).mpr hlo
  · apply (lt_div_iff₀ hm0).mpr
    simpa only [Nat.cast_add,Nat.cast_one,index] using hhi

theorem source_left_valid {m : ℕ} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (start : Node) (hs : (199/100:ℝ) ≤ start.ratio) :
    Valid .even (point m (index m start)) := by
  have hcell := source_cell hm start (by linarith)
  rw [point_succ] at hcell
  change 198/100 ≤ point m (index m start)
  linarith [hcell.2]

theorem source_inverse_weight {m : ℕ} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (start : Node) (hlo : (199/100:ℝ) ≤ start.ratio) (hhi : start.ratio ≤ 23/10) :
    1/weight .even (point m (index m start)) ≤ initialConstant := by
  have hu := source_left_valid hm hsmall start hlo
  have hEnd : Valid .even (23/10:ℝ) := by norm_num [Valid]
  have hcell := (source_cell hm start (by linarith)).1
  have hphi := TwoStepDensityBounds.weight_antitone hu hEnd (hcell.trans hhi)
  exact one_div_le_one_div_of_le (weight_pos hEnd) hphi

variable {w ell S : ℝ} {start : Node}

theorem source_coverage {m : ℕ} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (hi : start.side = .even) (hs : (199/100:ℝ) ≤ start.ratio) (j : ℕ) :
    ∀ᵐ p ∂pathLaw w ell S start 0, coveredParents m j .even {index m start} p := by
  change ∀ᵐ p ∂Measure.dirac (some (History.empty : History w ell S start)), coveredParents m j .even {index m start} p
  apply (ae_dirac_iff (show MeasurableSet {p | coveredParents m j .even {index m start} p} from trivial)).mpr
  refine ⟨hi,?_⟩
  intro _
  exact ⟨index m start,Finset.mem_singleton_self _,source_cell hm start (by linarith),source_left_valid hm hsmall start hs⟩

theorem source_grid_mass {m : ℕ} (hm : 1 ≤ m) (hs : 0 ≤ start.ratio) :
    mass w ell S start m 0 (index m start) = 1 := by
  have hcell : some (History.empty : History w ell S start) ∈ bin m (index m start) := source_cell hm start hs
  change Measure.dirac (some (History.empty : History w ell S start)) (bin m (index m start)) = 1
  rw [Measure.dirac_apply' _ (bin_measurable _ _),indicator_of_mem hcell,Pi.one_apply]

theorem bin_empty_above (hsS : start.ratio ≤ S) {m j : ℕ} (hhigh : S < point m j) :
    (bin (w:=w) (ell:=ell) (S:=S) (start:=start) m j) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  cases p with
  | none => exact False.elim hp
  | some g =>
    have hcap : g.node.ratio ≤ S := terminal_ratio_le hsS g.admissible
    exact ((mem_bin g m j).mp hp).1.not_gt (hcap.trans_lt hhigh)

theorem mass_zero_above (hsS : start.ratio ≤ S) {m j : ℕ} (hhigh : S < point m j) (n : ℕ) :
    mass w ell S start m n j = 0 := by
  rw [mass,bin_empty_above hsS hhigh,measure_empty]

end NumberTheoryLean.SourceParentBin

end

end Erdos970

end OAI
