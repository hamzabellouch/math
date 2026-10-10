import OAI.MeasureTheory.Falconer.Recursion.ProfilePacking
import OAI.MeasureTheory.Falconer.Geometry.DyadicSeparation
import OAI.MeasureTheory.Falconer.Angular.AllDimensionalAngularProfileSum
import OAI.MeasureTheory.Falconer.Incidence.AngularTubeCount

namespace OAI

/-!
# The inverse-power sum for actual parallel-test centers

The critical kernel exponent is arbitrary here so the application can
use d/2. Every counted center belongs to the original normalized class.
-/

namespace Falconer.Regularization
open Set Metric MeasureTheory
variable {d : ℕ}

noncomputable def parallelTestCells (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) : Finset (CellPath d) :=
  occupiedCenterCells Q ρ p (Q.descendant P).center (10*((d:ℝ)+1)/(2:ℝ)^g)

noncomputable def parallelTestCount (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) (W : ℝ) (w : Sphere d) : ℕ :=
  finiteTubeCount (parallelTestCells Q ρ g p P)
    (fun c => (Q.descendant c).center-(Q.descendant P).center) W w

theorem parallel_inverse_power_sum (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) {s : ℝ} (hs : 0 ≤ s) {g p : ℕ} (hgp : g ≤ p)
    {P : CellPath d} (hP : P.length = p) :
    (∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
      (1/dist (Q.descendant c).center (Q.descendant P).center)^s) ≤
      ((parallelTestCells Q ρ g p P).card:ℝ)*((2:ℝ)^g)^s +
        ∑ j ∈ Finset.range (p-g),
          ((occupiedCenterCells Q ρ p (Q.descendant P).center (1/(2:ℝ)^(g+j))).card:ℝ)*
            ((2:ℝ)^(g+j+1))^s := by
  classical
  let S := (parallelTestCells Q ρ g p P).erase P
  let r := fun c => dist (Q.descendant c).center (Q.descendant P).center
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hsep (c : CellPath d) (hc : c ∈ S) : 1/(2:ℝ)^p ≤ r c := by
    have hc' := Finset.mem_of_mem_erase hc
    have hl := (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hc').1
    simpa only [hQ] using Q.centers_separated hside hl hP (Finset.ne_of_mem_erase hc)
  have hr (c : CellPath d) (hc : c ∈ S) : 0 < r c :=
    lt_of_lt_of_le (by positivity : 0 < 1/(2:ℝ)^p) (hsep c hc)
  have hh := sum_inverse_power_dyadic S r hs g (p-g) hr (fun c hc => by
    simpa only [Nat.add_sub_of_le hgp] using hsep c hc)
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card (Finset.erase_subset P (parallelTestCells Q ρ g p P))
  · apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro c hc
    obtain ⟨hc,hrc⟩ := Finset.mem_filter.mp hc
    have hc' := Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)
    exact Finset.mem_filter.mpr ⟨hc'.1,hc'.2.1,hrc⟩

noncomputable def parallelPackingConstant (d : ℕ) : ℕ :=
  max ((2*Nat.ceil (20*((d:ℝ)+1)+2*Real.sqrt d)+1)^d)
    ((2*Nat.ceil (2+2*Real.sqrt d)+1)^d)

theorem sourceClass_parallel_inverse_power (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath d} (hP : P.length = p) :
    (∑ c ∈ (parallelTestCells Q (sourceClass Q μ N B p₀) g p P).erase P,
      (1/dist (Q.descendant c).center (Q.descendant P).center)^s)/((2:ℝ)^p)^s ≤
      (parallelPackingConstant d:ℝ)*(1+(2:ℝ)^s*(p-g:ℕ))*
        ((2:ℝ)^N)^(PlanarFalconer.height
          (fun n : ℕ => sourceProfile Q μ N B p₀ n-s*(n:ℝ)/N) g p+2*((d:ℝ)+1)*lam) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  let m := sourceProfile Q μ N B p₀
  let E := 2*((d:ℝ)+1)*lam
  let ρ := sourceClass Q μ N B p₀
  let R : ℝ := (2:ℝ)^N
  let D : ℝ := parallelPackingConstant d
  have hpack {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) (x : Space d) {C : ℝ} (hC : 0 ≤ C) :=
    sourceClass_local_count Q hside μ hN hB hwidth hlarge hp₀ hgp hpN x hC
  have hbase : ((parallelTestCells Q ρ g p P).card:ℝ) ≤ D*R^(m p-m g+E) := by
    have hh := hpack hgp hpN (Q.descendant P).center (show 0 ≤ 10*((d:ℝ)+1) by positivity)
    simp only [hQ,div_one] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp only [D,parallelPackingConstant]
    have he : 2*(10*((d:ℝ)+1)) = 20*((d:ℝ)+1) := by ring
    rw [he]
    exact_mod_cast le_max_left ((2*Nat.ceil (20*((d:ℝ)+1)+2*Real.sqrt d)+1)^d)
      ((2*Nat.ceil (2+2*Real.sqrt d)+1)^d)
  have hterm (j : ℕ) (hj : j ∈ Finset.range (p-g)) :
      ((occupiedCenterCells Q ρ p (Q.descendant P).center (1/(2:ℝ)^(g+j))).card:ℝ) ≤
        D*R^(m p-m (g+j)+E) := by
    have hj' := Finset.mem_range.mp hj
    have hh := hpack (g := g+j) (p := p) (by omega) hpN (Q.descendant P).center
      (show (0:ℝ) ≤ 1 by norm_num)
    simp only [hQ,div_one,mul_one,Nat.cast_add] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp only [D,parallelPackingConstant]
    exact_mod_cast le_max_right ((2*Nat.ceil (20*((d:ℝ)+1)+2*Real.sqrt d)+1)^d)
      ((2*Nat.ceil (2+2*Real.sqrt d)+1)^d)
  have hsum := parallel_inverse_power_sum Q hQ ρ hs hgp hP
  have hb : (∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
      (1/dist (Q.descendant c).center (Q.descendant P).center)^s) ≤
      D*(R^(m p-m g+E)*((2:ℝ)^g)^s+
        ∑ j ∈ Finset.range (p-g), R^(m p-m (g+j)+E)*((2:ℝ)^(g+j+1))^s) := by
    apply hsum.trans
    rw [mul_add,Finset.mul_sum]
    apply add_le_add
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hbase (by positivity : 0 ≤ ((2:ℝ)^g)^s)
    · apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hterm j hj)
        (by positivity : 0 ≤ ((2:ℝ)^(g+j+1))^s)
  apply (div_le_div_of_nonneg_right hb (by positivity)).trans
  rw [mul_div_assoc]
  have hh := mul_le_mul_of_nonneg_left (angular_profile_power_sum m hN s E hgp)
    (show 0 ≤ D by dsimp [D]; positivity)
  simpa only [D,R,m,E,mul_assoc] using hh

end Falconer.Regularization

end OAI
