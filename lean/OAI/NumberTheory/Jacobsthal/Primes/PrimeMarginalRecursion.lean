import OAI.NumberTheory.Jacobsthal.Partitions.FiniteBinIntegral
import OAI.NumberTheory.Jacobsthal.Partitions.GridWeightComparison

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeGridKernel

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeKilledChain PrimeSideSupport PrimeGridGeometry

variable {w ell S : ℝ} {start : Node}

noncomputable def bin (m j : ℕ) : Set (ChainState w ell S start) :=
  ActualPrimeBins.liveBin (point m j) (point m (j+1))

theorem mem_bin (g : History w ell S start) (m j : ℕ) :
    some g ∈ bin m j ↔ g.node.ratio ∈ Ico (point m j) (point m (j+1)) := Iff.rfl

theorem bin_measurable (m j : ℕ) : MeasurableSet (bin (w:=w) (ell:=ell) (S:=S) (start:=start) m j) := trivial

theorem row_none (m j : ℕ) : chain w ell S start none (bin m j) = 0 := by
  rw [chain_none,Measure.dirac_apply' _ (bin_measurable m j),
    indicator_of_notMem (show (none:ChainState w ell S start) ∉ bin m j from ActualPrimeBins.not_mem_liveBin_none _ _)]

theorem row_zero_of_large_parent (g : History w ell S start) (m j : ℕ)
    (hlarge : point m j+width m+1 ≤ g.node.ratio) :
    chain w ell S start (some g) (bin m j) = 0 := by
  classical
  rw [bin,point_succ,ActualPrimeBins.chain_live_bin_formula]
  apply Finset.sum_eq_zero
  intro p hp
  have hlo := (Finset.mem_filter.mp hp).2.2.2.1
  have hmin := minRatio_ge_sub_one g.node.side g.node.ratio
  have hnot : ¬(point m j ≤ childRatio w g.node.gap p ∧ childRatio w g.node.gap p < point m j+width m) := by
    rintro ⟨_,ht⟩
    linarith
  rw [ite_eq_right hnot]

theorem row_zero_above_grid (g : History w ell S start) {m : ℕ} (hm : 1 ≤ m) (j : ℕ)
    (hlarge : point m (j+m+2) ≤ g.node.ratio) :
    chain w ell S start (some g) (bin m j) = 0 := by
  apply row_zero_of_large_parent
  rw [incoming_grid_end hm j] at hlarge
  linarith [width_nonneg m]

noncomputable def weakIndices (m j : ℕ) (i : Side) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 (j+m+1)).filter (fun k => Valid i (point m k))

theorem weak_parent_cover (g : History w ell S start) {m : ℕ} (hm : 1 ≤ m)
    (hsmall : width m ≤ 1/100) (j : ℕ) (hv : Valid g.node.side g.node.ratio) (hg : WeakRegular g.node)
    (hupper : g.node.ratio < point m (j+m+2)) :
    ∃ k ∈ weakIndices m j g.node.side, some g ∈ bin m k := by
  classical
  obtain ⟨k,hk,hbin⟩ := finite_grid_cover (J:=j+m+1) hm (valid_pos hv).le (by simpa only [Nat.add_assoc] using hupper)
  exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,hk⟩,weak_bin_domain hm hsmall hg hbin⟩,hbin⟩

theorem regular_parent_cover (g : History w ell S start) {m : ℕ} (hm : 1 ≤ m)
    (j : ℕ) (hv : Valid g.node.side g.node.ratio) (hg : Regular g.node)
    (hupper : g.node.ratio < point m (j+m+2)) :
    ∃ k ∈ Finset.Icc (lowerIndex m g.node.side) (j+m+1),
      some g ∈ bin m k ∧ Valid g.node.side (point m k) := by
  obtain ⟨k,hk,hbin⟩ := finite_grid_cover (J:=j+m+1) hm (valid_pos hv).le (by simpa only [Nat.add_assoc] using hupper)
  have hdom := regular_bin_domain hm hg hbin
  exact ⟨k,Finset.mem_Icc.mpr ⟨hdom.1,hk⟩,hbin,hdom.2⟩

noncomputable def mass (w ell S : ℝ) (start : Node) (m n j : ℕ) : ℝ≥0∞ :=
  pathLaw w ell S start n (bin m j)

theorem mass_step (m n j : ℕ) :
    mass w ell S start m (n+1) j =
      ∫⁻ p,chain w ell S start p (bin m j) ∂pathLaw w ell S start n := by
  have hp : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
  change ((chain w ell S start)^(n+1)) (some History.empty) (bin m j) = _
  rw [hp]
  exact Kernel.comp_apply' _ _ _ (bin_measurable m j)

end NumberTheoryLean.PrimeGridKernel

end

section


namespace NumberTheoryLean.PrimeMarginalRecursion

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeSideSupport
open PrimeGridGeometry PrimeGridKernel GridWeightComparison ExponentialMesh FiniteBinIntegral
open DerivativeWeights

noncomputable def entry (L κ w S : ℝ) (m : ℕ) (i : Side) (j k : ℕ) : ℝ :=
  (1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*Real.exp (L*(1+S)^3*mesh κ w)*
    width m*W (point m j)*(weight i.flip (point m j)/weight i (point m k))

def coveredParents {w ell S : ℝ} {start : Node} (m j : ℕ) (i : Side) (I : Finset ℕ) :
    ChainState w ell S start → Prop
  | none => True
  | some g => g.node.side = i ∧ (g.node.ratio < point m (j+m+2) →
      ∃ k ∈ I, some g ∈ bin m k ∧ Valid i (point m k))

theorem weak_coverage {w ell S : ℝ} {start : Node} (hs : Valid start.side start.ratio)
    (hi : start.side = .even) {m : ℕ} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    ∀ᵐ p ∂pathLaw w ell S start n, coveredParents m j (sideAfter .even n) (weakIndices m j (sideAfter .even n)) p := by
  filter_upwards [pathLaw_side (w:=w) (ell:=ell) (S:=S) hi n,pathLaw_weak (w:=w) (ell:=ell) (S:=S) hs n hn] with p hside hweak
  cases p with
  | none => trivial
  | some g =>
    refine ⟨hside,?_⟩
    intro htop
    have hgv : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
    obtain ⟨k,hk,hbin⟩ := weak_parent_cover g hm hsmall j hgv hweak htop
    have hkV := weak_bin_domain hm hsmall hweak ((mem_bin g m k).mp hbin)
    exact ⟨k,by simpa only [hside] using hk,hbin,by simpa only [hside] using hkV⟩

theorem regular_coverage {w ell S : ℝ} {start : Node} (hs : Valid start.side start.ratio)
    (hi : start.side = .even) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) (hn : 2 ≤ n) (j : ℕ) :
    ∀ᵐ p ∂pathLaw w ell S start n, coveredParents m j (sideAfter .even n)
      (Finset.Icc (lowerIndex m (sideAfter .even n)) (j+m+1)) p := by
  filter_upwards [pathLaw_side (w:=w) (ell:=ell) (S:=S) hi n,pathLaw_regular (w:=w) (ell:=ell) (S:=S) (start:=start) n hn] with p hside hreg
  cases p with
  | none => trivial
  | some g =>
    refine ⟨hside,?_⟩
    intro htop
    have hgv : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
    obtain ⟨k,hk,hbin,hkV⟩ := regular_parent_cover g hm j hgv hreg htop
    exact ⟨k,by simpa only [hside] using hk,hbin,by simpa only [hside] using hkV⟩

theorem covered_recursion : ∃ κ₀ L : ℝ, 0 < κ₀ ∧ 0 < L ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ w₀ : ℝ, 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w →
    ∀ ell S : ℝ, 3 ≤ S → S ≤ (Real.log w)^3 → ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S →
      ∀ m n j : ℕ, 1 ≤ m → width m = mesh κ w → ∀ i : Side, ∀ I : Finset ℕ,
      Valid i.flip (point m j) → point m j ≤ S →
      (∀ᵐ p ∂pathLaw w ell S start n, coveredParents m j i I p) →
      mass w ell S start m (n+1) j ≤
        ∑ k ∈ I,ENNReal.ofReal (entry L κ w S m i j k)*mass w ell S start m n k := by
  obtain ⟨κ₀,L,hκ₀,hL,hparent⟩ := actual_parent_bin_upper
  refine ⟨κ₀,L,hκ₀,hL,?_⟩
  intro κ hκ hκle
  obtain ⟨w₀,hw₀,hrow⟩ := hparent κ hκ hκle
  refine ⟨w₀,hw₀,?_⟩
  intro w hw ell S hS3 hS start hell hr hs hsS m n j hm hmesh i I hjV hjS hcover
  classical
  have hEnvelope : ∀ᵐ p ∂pathLaw w ell S start n,
      chain w ell S start p (bin m j) ≤
        ∑ k ∈ I,ENNReal.ofReal (entry L κ w S m i j k)*((bin m k).indicator (fun _ => (1:ℝ≥0∞)) p) := by
    filter_upwards [hcover] with p hp
    cases p with
    | none => rw [row_none]; exact zero_le
    | some g =>
      by_cases hhigh : point m (j+m+2) ≤ g.node.ratio
      · rw [row_zero_above_grid g hm j hhigh]
        exact zero_le
      · obtain ⟨k,hk,hbin,hkV⟩ := hp.2 (lt_of_not_ge hhigh)
        have hgu : Valid g.node.side (point m k) := by rwa [hp.1]
        have hga : Valid g.node.side.flip (point m j) := by rwa [hp.1]
        have hgn : g.node.ratio ≤ S := terminal_ratio_le hsS g.admissible
        have hgBin := (mem_bin g m k).mp hbin
        have hgb : g.node.ratio ≤ point m k+mesh κ w := by
          rw [point_succ,hmesh] at hgBin
          exact hgBin.2.le
        have hb := hrow w hw ell S hS3 hS start hell hr hs g (point m k) (point m j)
          hgu hga hgn hjS hgBin.1 hgb
        have hentry : chain w ell S start (some g) (bin m j) ≤ ENNReal.ofReal (entry L κ w S m i j k) := by
          simpa only [bin,point_succ,hmesh,entry,hp.1] using hb
        calc
          _ ≤ ENNReal.ofReal (entry L κ w S m i j k) := hentry
          _ = ENNReal.ofReal (entry L κ w S m i j k)*((bin m k).indicator (fun _ => (1:ℝ≥0∞)) (some g)) := by
            rw [indicator_of_mem hbin,mul_one]
          _ ≤ _ := Finset.single_le_sum (s:=I) (a:=k)
            (f:=fun l => ENNReal.ofReal (entry L κ w S m i j l)*((bin m l).indicator (fun _ => (1:ℝ≥0∞)) (some g)))
            (fun _ _ => zero_le) hk
  rw [mass_step]
  calc
    _ ≤ ∫⁻ p,∑ k ∈ I,ENNReal.ofReal (entry L κ w S m i j k)*((bin m k).indicator (fun _ => (1:ℝ≥0∞)) p)
        ∂pathLaw w ell S start n := lintegral_mono_ae hEnvelope
    _ = _ := integrate_bin_envelope (pathLaw w ell S start n) I (bin m)
      (fun k _ => bin_measurable m k) (entry L κ w S m i j)

theorem weak_recursion : ∃ κ₀ L : ℝ, 0 < κ₀ ∧ 0 < L ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ w₀ : ℝ, 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w →
    ∀ ell S : ℝ, 3 ≤ S → S ≤ (Real.log w)^3 → ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S → start.side = .even →
      ∀ m n j : ℕ, 1 ≤ m → width m = mesh κ w → width m ≤ 1/100 → 1 ≤ n →
      Valid (sideAfter .even n).flip (point m j) → point m j ≤ S →
      mass w ell S start m (n+1) j ≤
        ∑ k ∈ weakIndices m j (sideAfter .even n),
          ENNReal.ofReal (entry L κ w S m (sideAfter .even n) j k)*mass w ell S start m n k := by
  obtain ⟨κ₀,L,hκ₀,hL,hrec⟩ := covered_recursion
  refine ⟨κ₀,L,hκ₀,hL,?_⟩
  intro κ hκ hκle
  obtain ⟨w₀,hw₀,hrec⟩ := hrec κ hκ hκle
  refine ⟨w₀,hw₀,?_⟩
  intro w hw ell S hS3 hS start hell hr hs hsS hi m n j hm hmesh hsmall hn hjV hjS
  apply hrec w hw ell S hS3 hS start hell hr hs hsS m n j hm hmesh (sideAfter .even n)
    (weakIndices m j (sideAfter .even n)) hjV hjS
  exact weak_coverage hs hi hm hsmall n hn j

theorem regular_recursion : ∃ κ₀ L : ℝ, 0 < κ₀ ∧ 0 < L ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ w₀ : ℝ, 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w →
    ∀ ell S : ℝ, 3 ≤ S → S ≤ (Real.log w)^3 → ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S → start.side = .even →
      ∀ m n j : ℕ, 1 ≤ m → width m = mesh κ w → 2 ≤ n →
      Valid (sideAfter .even n).flip (point m j) → point m j ≤ S →
      mass w ell S start m (n+1) j ≤
        ∑ k ∈ Finset.Icc (lowerIndex m (sideAfter .even n)) (j+m+1),
          ENNReal.ofReal (entry L κ w S m (sideAfter .even n) j k)*mass w ell S start m n k := by
  obtain ⟨κ₀,L,hκ₀,hL,hrec⟩ := covered_recursion
  refine ⟨κ₀,L,hκ₀,hL,?_⟩
  intro κ hκ hκle
  obtain ⟨w₀,hw₀,hrec⟩ := hrec κ hκ hκle
  refine ⟨w₀,hw₀,?_⟩
  intro w hw ell S hS3 hS start hell hr hs hsS hi m n j hm hmesh hn hjV hjS
  apply hrec w hw ell S hS3 hS start hell hr hs hsS m n j hm hmesh (sideAfter .even n)
    (Finset.Icc (lowerIndex m (sideAfter .even n)) (j+m+1)) hjV hjS
  exact regular_coverage hs hi hm n hn j

end NumberTheoryLean.PrimeMarginalRecursion

end

end Erdos970

end OAI
