import OAI.Analysis.SignedDisk.ActualLabels1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks ActualLabels GeometricFilter Finset

lemma path_filtered_cost {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {l : ℕ} (hl : l ≤ m) {x : ℂ} (hx : x ∈ neighborhood (scale r (m-l)) (pathVertex q p l))
    {i : ℕ} (hi : i ≤ m) (hil : i ≤ l+1) :
    switchCost h (fun j => scale r (m-j)) x i+derivativeCost h (fun j => scale r (m-j)) x i ≤
      spatialConstant*filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))) i := by
  apply filtered_spatial_cost h _ _ x _ i (fun j _ => scale_pos hr (m-j))
    (fun j hj => descending_step r (by omega))
  · intro j hj
    exact (path_neighborhood_geometry v hr hp hl hx (by omega : j ≤ m) (by omega)).2.1
  · intro j hj
    exact (path_neighborhood_geometry v hr hp hl hx (by omega : j ≤ m) (by omega)).2.2
  · exact (path_neighborhood_geometry v hr hp hl hx hi hil).1

lemma path_cellCost {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {l : ℕ} (hl : l ≤ m) :
    cellCost h (fun j => scale r (m-j)) m l (pathVertex q p l) ≤
      spatialConstant*(filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))) l+
        filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))) (l+1)+
        filt (filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p)))) l)+
      (if l=m then 1 else 0) := by
  let rs := fun j => scale r (m-j)
  let c := energyRate h rs (pathVertex q p) (point r (lastVertex q p))
  have hs (i : ℕ) (hi : i ≤ m) (hil : i ≤ l+1) :
      localSup (fun x => switchCost h rs x i) (rs l) (pathVertex q p l) ≤ spatialConstant*filt c i := by
    apply localSup_le (scale_pos hr _).le
    intro x hx
    have hh := path_filtered_cost h v hr hp hl hx hi hil
    change switchCost h rs x i+derivativeCost h rs x i ≤ spatialConstant*filt c i at hh
    linarith [derivativeCost_nonneg h rs x i (scale_pos hr _).le]
  have ht (i : ℕ) (hi : i ≤ l) :
      localSup (fun x => derivativeCost h rs x i) (rs l) (pathVertex q p l) ≤ spatialConstant*filt c i := by
    apply localSup_le (scale_pos hr _).le
    intro x hx
    have hh := path_filtered_cost h v hr hp hl hx (show i ≤ m by omega) (show i ≤ l+1 by omega)
    change switchCost h rs x i+derivativeCost h rs x i ≤ spatialConstant*filt c i at hh
    linarith [switchCost_nonneg h rs x i]
  have hT := filt_mono_on l ht
  rw [filt_mul] at hT
  have hnext : (if l=m then 1 else localSup (fun x => switchCost h rs x (l+1)) (rs l) (pathVertex q p l)) ≤
      spatialConstant*filt c (l+1)+(if l=m then 1 else 0) := by
    split_ifs with he
    · have hh := mul_nonneg spatialConstant_pos.le (filt_nonneg (energyRate_nonneg h rs (pathVertex q p) (point r (lastVertex q p))) (l+1))
      linarith
    · simpa only [add_zero] using hs (l+1) (by omega) le_rfl
  have hcur := hs l hl (by omega)
  change cellCost h rs m l (pathVertex q p l) ≤ _
  dsimp only [cellCost]
  change _ ≤ spatialConstant*(filt c l+filt c (l+1)+filt (filt c) l)+(if l=m then 1 else 0)
  linarith

lemma path_cellCost_sum {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {b : ℕ} (hb : b ≤ m) :
    (∑ l ∈ Ico b (m+1), cellCost h (fun j => scale r (m-j)) m l (pathVertex q p l)) ≤
      spatialConstant*(8*∑ i ∈ Ico b (m+1),
        energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p)) i+130)+1 := by
  let c := energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))
  have hc0 := energyRate_nonneg h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))
  have hcA := energyRate_le_five h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))
  have h1 := filt_tail (by norm_num : (0:ℝ) ≤ 5) hc0 hcA hb
  have h2 := shifted_tail (by norm_num : (0:ℝ) ≤ 5) hc0 hcA hb
  have h3 := double_tail (by norm_num : (0:ℝ) ≤ 5) hc0 hcA hb
  have hs := sum_le_sum (fun l (hl : l ∈ Finset.Ico b (m+1)) => path_cellCost h v hr hp (show l ≤ m by have := Finset.mem_Ico.mp hl; omega))
  change _ ≤ ∑ l ∈ Ico b (m+1), (spatialConstant*(filt c l+filt c (l+1)+filt (filt c) l)+(if l=m then 1 else 0)) at hs
  simp only [sum_add_distrib,← mul_sum] at hs
  have he : (∑ l ∈ Ico b (m+1), if l=m then (1:ℝ) else 0) = 1 := by simp [hb]
  rw [he] at hs
  change _ ≤ spatialConstant*(8*∑ i ∈ Ico b (m+1), c i+130)+1
  have hh : (∑ i ∈ Ico b (m+1), filt c i)+(∑ i ∈ Ico b (m+1), filt c (i+1))+
      (∑ i ∈ Ico b (m+1), filt (filt c) i) ≤ 8*∑ i ∈ Ico b (m+1), c i+130 := by linarith
  exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_left hh spatialConstant_pos.le])

open DyadicHats IntrinsicMarks ActualLabels GeometricFilter DirectionNeighbors Finset

def packingCharge {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (m : ℕ) (q : Grid N) : List (Grid N) → ℝ :=
  spatialCharge (fun j z => cellCost h (fun i => scale r (m-i)) m (m-j) z) m q

lemma packingCharge_path {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {b : ℕ} (hb : b ≤ p.length) :
    pathCharge (packingCharge h r m q) p b ≤
      8*spatialConstant*particleSwitches h r m q p b+
      8*spatialConstant*pathCharge (pathEnergy h r m q) p b+(130*spatialConstant+1) := by
  have hlen := active_length v hp
  have hs := path_cellCost_sum h v hr hp (show b ≤ m by omega)
  have hC : pathCharge (packingCharge h r m q) p b =
      ∑ i ∈ Ico b (m+1), cellCost h (fun j => scale r (m-j)) m i (pathVertex q p i) := by
    rw [pathCharge_sum,hlen]
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ m := by have := Finset.mem_Ico.mp hi; omega
    simp only [packingCharge,spatialCharge,List.length_take,hlen,min_eq_left hi',
      Nat.sub_sub_self hi',pathVertex]
  have hE : (∑ i ∈ Ico b (m+1), energyRate h (fun j => scale r (m-j)) (pathVertex q p)
      (point r (lastVertex q p)) i) =
      particleSwitches h r m q p b+pathCharge (pathEnergy h r m q) p b := by
    rw [pathCharge_sum]
    simp only [particleSwitches,pathSwitches,hlen,energyRate,sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ m := by have := Finset.mem_Ico.mp hi; omega
    simp only [pathEnergy,List.length_take,hlen,min_eq_left hi',pathVertex]
  rw [hC]
  rw [hE] at hs
  linarith

lemma tree_packing_bound {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (q : Grid N) :
    nodeCharge (tree v m 1 q) (packingCharge h r m q) ≤
      8*spatialConstant*particleEval (tree v m 1 q) (particleSwitches h r m q)+
      8*spatialConstant*nodeCharge (tree v m 1 q) (pathEnergy h r m q)+
      (130*spatialConstant+1)*terminalMass (tree v m 1 q) := by
  have hs := particleEval_mono_active (tree v m 1 q)
    (F := pathCharge (packingCharge h r m q))
    (fun p b hp hb => packingCharge_path h v hr hp hb)
  simp only [particleEval_add,particleEval_smul,particleEval_const,particle_occupancy] at hs
  nlinarith only [hs]

def packingConstant : ℝ :=
  8*spatialConstant*(2560004+2000000*(576*(4097:ℝ)^2))+
  8*spatialConstant*(576*(4097:ℝ)^2)+(130*spatialConstant+1)
lemma packingConstant_pos : 0 < packingConstant := by
  dsimp [packingConstant]
  have := spatialConstant_pos
  positivity

theorem spatial_packing {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) :
    (∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale r j) q*
      cellCost h (fun i => scale r (m-i)) m (m-j) q) ≤
      packingConstant*(∫ y, ‖h y‖) := by
  have hs := sum_le_sum (fun q (_ : q ∈ (univ : Finset (Grid N))) =>
    tree_packing_bound h (fun q => vectorMass h r q) hr m q)
  simp only [sum_add_distrib,← mul_sum] at hs
  have hleft : (∑ q : Grid N, nodeCharge (tree (fun q => vectorMass h r q) m 1 q)
      (packingCharge h r m q)) =
      ∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale r j) q*
        cellCost h (fun i => scale r (m-i)) m (m-j) q := by
    unfold packingCharge
    rw [sum_nodeCharge]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro q hq
    rw [← vectorMass_coeff hr hR hN hh hsupp]
    rfl
  rw [hleft,sum_energyCharge hr hR hN hh hsupp,sum_terminalMass] at hs
  have hS := forest_switch_budget hr hR hN hh hsupp m
  have hE := neighbor_energy_budget hr hR hN hh hsupp (m+1)
  have hM := sum_scalarMass_grid_le (N := N) hh r
  change (∑ q : Grid N, ‖vectorMass h r q‖) ≤ ∫ y, ‖h y‖ at hM
  have hcoef : 0 ≤ 8*spatialConstant := by have := spatialConstant_pos; positivity
  have hcoef' : 0 ≤ 130*spatialConstant+1 := by have := spatialConstant_pos; positivity
  dsimp only [packingConstant]
  nlinarith only [hs,mul_le_mul_of_nonneg_left hS hcoef,
    mul_le_mul_of_nonneg_left hE hcoef,mul_le_mul_of_nonneg_left hM hcoef']
end ActualMarkTrees

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces

def rootMass {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) : ℝ :=
  ∑ q ∈ S, scalarMass h (scale r k) q
lemma rootMass_nonneg {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) :
    0 ≤ rootMass h r k S := sum_nonneg (fun _ _ => norm_nonneg _)

def sizeErrors {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) : Option (ErrorIndex N k) → ErrorPiece 2
  | none => unitPiece (rescale p (scale r k) (rootSum h r k S n))
      (integrable_rescale (rootSum_integrable hh r k S n) p (scale_pos hr k).ne') 2
  | some i => smallPiece hh hr k p S n i

lemma sizeErrors_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : n ∈ fixedPalette.labels) :
    errorPrice (sizeErrors hr hh k p S n) (1/100) ≤
      (scale r k)⁻¹*(4*rootMass h r k S+2*cellPrice N r h k S) := by
  have hb : (sizeErrors hr hh k p S n none).mass ≤ (scale r k)⁻¹*4*rootMass h r k S := by
    change (∫ X, ‖rescale p (scale r k) (rootSum h r k S n) X‖) ≤ _
    rw [mass_rescale _ _ (scale_pos hr k)]
    simpa only [mul_assoc,rootMass] using mul_le_mul_of_nonneg_left
      (rootSum_mass hr hR hN hh hsupp k S (fixedPalette.unit n hn)) (inv_nonneg.mpr (scale_pos hr k).le)
  have hs := smallPiece_common_price hr hR hN hh hsupp k p S hn
  change (∑ i, (smallPiece hh hr k p S n i).size^(1/100:ℝ)*
    (smallPiece hh hr k p S n i).mass) ≤ _ at hs
  simp only [errorPrice,Fintype.sum_option,show (sizeErrors hr hh k p S n none).size = 1 from rfl,
    Real.one_rpow,one_mul]
  change (sizeErrors hr hh k p S n none).mass + (∑ i, (smallPiece hh hr k p S n i).size^(1/100:ℝ)*(smallPiece hh hr k p S n i).mass) ≤ _
  linarith

lemma sizeErrors_gradient {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {g : ℂ → ℝ} (hg : Differentiable ℝ g)
    (hh : Integrable (gradient g)) (hsupp : ∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (p : ℤ × ℤ) {n : ℂ} (hn : ‖n‖ = 1) (X : ℂ) (hX : ‖X‖ ≤ 12) :
    (∑ i, (sizeErrors hr hh k (point (scale r k) p) (cellRoots N p) n i).density X) =
      gradient (fun Y => g (point (scale r k) p+scale r k • Y)) X := by
  rw [Fintype.sum_option]
  change rescale _ _ (rootSum _ _ _ _ _) X+
    (∑ i : ErrorIndex N k, (smallPiece hh hr k _ _ n i).density X) = _
  rw [smallPiece_sum,gradient_affine hg]
  simp only [rescale,← smul_add,rootSum,← sum_add_distrib]
  have he := sum_congr rfl (fun q (_ : q ∈ cellRoots N p) =>
    (vector_decomposition hr hR hN hsupp k q hn (point (scale r k) p+scale r k • X)).symm)
  rw [he,← sum_smul,cell_partition (scale_pos hr k) (scale_index_bound hr hR hN k) hsupp p X hX]

/-- The endpoint-bin gradient price, with all root terms retained rather than
silently using the cone estimate at one-sided maximizing radii. -/
theorem size_cell_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ X in Q, F X) ≤ ENNReal.ofReal (C*(scale r k)⁻¹*
        (rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ X, ‖X‖ ≤ 2 → ∀ t,
        EndpointRadius (fun Y => g (point (scale r k) p+scale r k • Y)) X t →
        ENNReal.ofReal ‖∫ Y in Metric.ball X t,
          gradient (fun Z => g (point (scale r k) p+scale r k • Z)) Y‖ ≤ F X := by
  obtain ⟨C,hC,hmajor⟩ := size_majorant (by norm_num : (0:ℝ) ≤ 2)
  refine ⟨4*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hsupp k p n hn Q hQ
  let b := sizeErrors hr hh k (point (scale r k) p) (cellRoots N p) n
  have hg' : ContDiff ℝ 1 (fun Y => g (point (scale r k) p+scale r k • Y)) := hg.comp (by fun_prop)
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor b _ hg' Q hQ
  refine ⟨F,hFm,?_,?_⟩
  · apply hFi.trans
    apply ENNReal.ofReal_le_ofReal
    have hb := sizeErrors_price hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn
    have hD : 0 ≤ cellPrice N r (gradient g) k (cellRoots N p) :=
      sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
    change errorPrice b (1/100) ≤ _ at hb
    have hrk := scale_pos hr k
    nlinarith [mul_le_mul_of_nonneg_left hb hC.le,inv_nonneg.mpr hrk.le,
      mul_nonneg (inv_nonneg.mpr hrk.le) hD]
  · intro X hX t ht
    apply hFb X _ t ht
    filter_upwards with Y hY
    apply sizeErrors_gradient hr hR hN (hg.differentiable one_ne_zero) hh hsupp k p (fixedPalette.unit n hn)
    have hy : ‖Y-X‖ < 3 := by simpa only [Metric.mem_ball,dist_eq_norm] using hY
    have htri := norm_add_le (Y-X) X
    rw [sub_add_cancel] at htri
    linarith
end CommonPrices

namespace PlanePotential
open LocalCancellation

lemma green_restrict_density {ψ : ℂ → ℝ} {R X : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hRX : R ≤ X)
    (β : ℂ → ℂ) {x : ℂ} (hx : ‖x‖ ≤ X) (y : ℂ) :
    ⟪green ψ x y, ({y : ℂ | ‖y‖ ≤ X}.indicator β) y⟫ = ⟪green ψ x y,β y⟫ := by
  by_cases hy : ‖y‖ ≤ X
  · simp [hy]
  · rw [green_eq_zero_of_outside hψs hRX hx (lt_of_not_ge hy)]
    simp

lemma green_root_lp_local {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hX : 0 < X)
    (hβ : Integrable β) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*X)^(1/2:ℝ))) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let β' := {y : ℂ | ‖y‖ ≤ X}.indicator β
  have hi : Integrable β' := hβ.indicator (measurableSet_le measurable_norm measurable_const)
  have hs : ∀ y, β' y ≠ 0 → ‖y‖ ≤ X := by
    intro y hy
    by_contra hn
    exact hy (by simp [β',hn])
  have h := green_root_lp hψm hψs hψB hM hB (show 0 < X+X by linarith) hi hs
  have he : (fun x => (ENNReal.ofReal |∫ y, ⟪green ψ x y,β' y⟫|)^(3/2:ℝ)) =ᵐ[volume.restrict {x : ℂ | ‖x‖ ≤ X}]
      (fun x => (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) := by
    filter_upwards [ae_restrict_mem (measurableSet_le measurable_norm measurable_const)] with x hx
    congr 3
    exact integral_congr_ae (ae_of_all _ (green_restrict_density hψs hRX β hx))
  rw [lintegral_congr_ae he] at h
  have hm : (∫ y, ‖β' y‖) ≤ ∫ y, ‖β y‖ :=
    integral_mono hi.norm hβ.norm (fun y => norm_indicator_le_norm_self β y)
  have hm' := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hm) (by norm_num : (0:ℝ) ≤ 3/2)
  have h' := h.trans (mul_le_mul_right hm' _)
  simpa only [show 2*(X+X)=4*X by ring] using h'

lemma green_zero_piece_lp_ae {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z : ℂ) (hβ : Integrable β) (hzero : ∫ y, β y = 0)
    (hβs : ∀ᵐ y, β y ≠ 0 → ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((8*Real.pi*(2*B*(R+X)^2)^(3/2:ℝ)+
      Real.pi*(8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)^(3/2:ℝ))*a^(1/2:ℝ)) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let β' := {y : ℂ | ‖y-z‖ ≤ a}.indicator β
  have he : β' =ᵐ[volume] β := by
    filter_upwards [hβs] with y hy
    by_cases hs : ‖y-z‖ ≤ a
    · simp [β',hs]
    · have hz : β y = 0 := by by_contra hn; exact hs (hy hn)
      simp [β',hs,hz]
  have hi : Integrable β' := hβ.congr he.symm
  have hz : ∫ y, β' y = 0 := (integral_congr_ae he).trans hzero
  have hs : ∀ y, β' y ≠ 0 → ‖y-z‖ ≤ a := by
    intro y hy
    by_contra hn
    exact hy (by simp [β',hn])
  have hp (x : ℂ) : (∫ y, ⟪green ψ x y,β' y⟫) = ∫ y, ⟪green ψ x y,β y⟫ :=
    integral_congr_ae (he.mono (fun y hy => by simpa only using congrArg (fun z => ⟪green ψ x y,z⟫) hy))
  have hm : (∫ y, ‖β' y‖) = ∫ y, ‖β y‖ := integral_congr_ae (he.mono (fun y hy => by simpa only using congrArg norm hy))
  simpa only [hp,hm] using green_zero_piece_lp hψm hψs hψB hψL hM hB hL ha z hi hz hs

/-- The local decomposition theorem does not demand artificial bounded support
of the original densities: the actual Green kernel vanishes outside the
observation ball. -/
theorem green_decomposition_norm_local {ι : Type*} [Fintype ι]
    {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ 1 g) {D R X B : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1)
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hX : 0 < X)
    (β : ι → ℂ → ℂ) (hβ : ∀ i, Integrable (β i))
    (hdecomp : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β i y) :
    eLpNorm (fun x => g x-∫ z, ψ z*g z) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ≤
      ∑ i, eLpNorm (fun x => ∫ y, ⟪green ψ x y,β i y⟫) (3/2)
        (volume.restrict {x : ℂ | ‖x‖ ≤ X}) := by
  let β' := fun i => {y : ℂ | ‖y‖ ≤ X}.indicator (β i)
  have hi (i : ι) : Integrable (β' i) := (hβ i).indicator (measurableSet_le measurable_norm measurable_const)
  have hs (i : ι) (y : ℂ) (hy : β' i y ≠ 0) : ‖y‖ ≤ X := by
    by_contra hn
    exact hy (by simp [β',hn])
  have hd : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β' i y := by
    filter_upwards [hdecomp] with y hy hY
    simpa [β',hY] using hy hY
  have h := green_decomposition_norm hψ hψc hg hD hψ1 hψs hψB hRX hM hB
    (show 0 < X+X by linarith) β' hi hs hd
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro i _
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_norm measurable_const)] with x hx
  exact integral_congr_ae (ae_of_all _ (green_restrict_density hψs hRX (β i) hx))

/-- Uniform fractional small-support gain expressed in the common price
exponent 1/100, including the unrestricted unit-size terms. -/
theorem exists_green_price : ∃ (ψ : ℂ → ℝ) (C : ℝ), 0 < C ∧
    ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∫ z, ψ z) = 1 ∧
    (∀ z, ψ z ≠ 0 → ‖z‖ ≤ 1) ∧
    ∀ b : ErrorPiece 2,
      eLpNorm (fun x => ∫ y, ⟪green ψ x y,b.density y⟫) (3/2)
        (volume.restrict {x : ℂ | ‖x‖ ≤ 8}) ≤
        ENNReal.ofReal (C*b.size^(1/100:ℝ)*b.mass) := by
  obtain ⟨ψ,B,L,hB,hL,hψ,hψc,hψ1,hψs,hψB,hψL⟩ := exists_kernel_cutoff
  let A : ℝ := (2*B*(1+8)^2)^(3/2:ℝ)*(4*Real.pi*(4*8)^(1/2:ℝ))
  let Z : ℝ := 8*Real.pi*(2*B*(1+8)^2)^(3/2:ℝ)+
    Real.pi*(8*B*(1+8)^2+(64/3:ℝ)*L*(1+8)^3)^(3/2:ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let C : ℝ := A^(2/3:ℝ)+Z^(2/3:ℝ)*2^(1/3:ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ψ,C,hC,hψ,hψc,hψ1,hψs,?_⟩
  intro b
  have hb0 := b.size_pos.le
  have hm0 := b.mass_nonneg
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (3/2:ℝ≥0∞) ≠ 0) (by finiteness)
    (potential_aestronglyMeasurable _ (green_measurable ψ hψ.continuous.measurable) b.integrable)]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  by_cases hb : b.size < 1
  · have ha : 0 < 2*b.size := mul_pos (by norm_num) b.size_pos
    have hp := green_zero_piece_lp_ae hψ.continuous.measurable hψs hψB hψL (by norm_num : (0:ℝ) < 1+8)
      hB hL ha b.center b.integrable (b.zero_mass hb) (b.support hb)
    have hn := eLpNorm_three_halves_bound _ hp
    change _ ≤ (ENNReal.ofReal (Z*(2*b.size)^(1/2:ℝ)))^(2/3:ℝ)*ENNReal.ofReal b.mass at hn
    have he : (ENNReal.ofReal (Z*(2*b.size)^(1/2:ℝ)))^(2/3:ℝ)*ENNReal.ofReal b.mass =
        ENNReal.ofReal (Z^(2/3:ℝ)*2^(1/3:ℝ)*b.size^(1/3:ℝ)*b.mass) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow hZ (by positivity),← Real.rpow_mul (by positivity),show (1/2:ℝ)*(2/3)=1/3 by norm_num,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) b.size_pos.le]
      ring
    rw [he] at hn
    apply hn.trans (ENNReal.ofReal_le_ofReal _)
    have hbpow : b.size^(1/3:ℝ) ≤ b.size^(1/100:ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge b.size_pos b.size_le_one (by norm_num)
    have hZC : Z^(2/3:ℝ)*2^(1/3:ℝ) ≤ C := by dsimp [C]; linarith [Real.rpow_nonneg hA (2/3)]
    exact mul_le_mul_of_nonneg_right
      (le_trans (mul_le_mul_of_nonneg_left hbpow (by positivity))
        (mul_le_mul_of_nonneg_right hZC (by positivity))) b.mass_nonneg
  · have hb1 : b.size = 1 := le_antisymm b.size_le_one (le_of_not_gt hb)
    have hp := green_root_lp_local hψ.continuous.measurable hψs hψB (by norm_num : (1:ℝ) ≤ 8)
      (by norm_num : (0:ℝ) < 1+8) hB (by norm_num : (0:ℝ) < 8) b.integrable
    have hn := eLpNorm_three_halves_bound _ hp
    change _ ≤ (ENNReal.ofReal A)^(2/3:ℝ)*ENNReal.ofReal b.mass at hn
    rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num),← ENNReal.ofReal_mul (by positivity)] at hn
    simp only [hb1,Real.one_rpow,mul_one]
    apply hn.trans (ENNReal.ofReal_le_ofReal _)
    apply mul_le_mul_of_nonneg_right _ b.mass_nonneg
    dsimp [C]
    linarith [mul_nonneg (Real.rpow_nonneg hZ (2/3)) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (1/3))]
end PlanePotential

end SignedDisk

end

end OAI
