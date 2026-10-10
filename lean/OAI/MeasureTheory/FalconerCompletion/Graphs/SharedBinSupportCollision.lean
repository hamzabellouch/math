import Mathlib
import OAI.MeasureTheory.Falconer.Geometry.BinBands
import OAI.MeasureTheory.Falconer.Geometry.BinEstimates
import OAI.MeasureTheory.Falconer.Geometry.BinOffsets
import OAI.MeasureTheory.Falconer.Geometry.Bins
import OAI.MeasureTheory.Falconer.Geometry.FiniteBinComparison
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.InteriorPolicy
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Estimates.NormLinearErrorIdentity

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal

lemma shared_bin_support_collisionND (α α' β β' : Measure ℝ)
    [IsFiniteMeasure β] [IsFiniteMeasure β']
    (hα : α ≤ β) (hα' : α' ≤ β') {c c' δ w : ℝ}
    (hβ : ∀ᵐ x ∂β, |x-c| ≤ δ) (hβ' : ∀ᵐ x ∂β', |x-c'| ≤ δ)
    (hbin : ∃ k : ℤ, α (realBin w k) ≠ 0 ∧ α' (realBin w k) ≠ 0) :
    (β.prod β') {z : ℝ × ℝ | |z.1-z.2| ≤ w+4*δ}=(β univ)*(β' univ) := by
  obtain ⟨k,hk,hk'⟩ := hbin
  obtain ⟨x,hxbin,hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hk
    (ae_restrict_of_ae (hβ.filter_mono (ae_mono hα)))
  obtain ⟨y,hybin,hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hk'
    (ae_restrict_of_ae (hβ'.filter_mono (ae_mono hα')))
  have hxy := realBin_diameter w k hxbin hybin
  have hgood : ∀ᵐ z ∂β.prod β', |z.1-z.2| ≤ w+4*δ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hβ,
      Measure.quasiMeasurePreserving_snd.ae hβ'] with z hz hz'
    obtain ⟨ha,hb⟩ := abs_le.mp hz
    obtain ⟨hc,hd⟩ := abs_le.mp hz'
    obtain ⟨he,hf⟩ := abs_le.mp hx
    obtain ⟨hg,hh⟩ := abs_le.mp hy
    obtain ⟨hi,hj⟩ := abs_le.mp hxy
    apply abs_le.mpr
    constructor <;> linarith
  rw [measure_congr (Filter.eventuallyEqSet_univ.mpr hgood),← univ_prod_univ,Measure.prod_prod]

theorem finite_positive_bin_assemblyND {ι : Type*} (S : Finset ι)
    (α β : ι → Measure ℝ) [∀ i, IsFiniteMeasure (α i)] [∀ i, IsFiniteMeasure (β i)]
    (c : ι → ℝ) (δ w W : ℝ) (F : ℝ≥0∞)
    (hle : ∀ i ∈ S, α i ≤ β i)
    (hsupp : ∀ i ∈ S, ∀ᵐ x ∂β i, |x-c i| ≤ δ)
    (hnorm : ∀ i ∈ S, (binL2Norm (α i) w)^2 ≤ F*((β i) univ)^2)
    (hW : w+4*δ ≤ W) :
    (binL2Norm (∑ i ∈ S, α i) w)^2 ≤
      F*((∑ i ∈ S, β i).prod (∑ i ∈ S, β i)) {z : ℝ × ℝ | |z.1-z.2| ≤ W} := by
  apply (finite_bin_collision_comparison S α β w
    {z : ℝ × ℝ | |z.1-z.2| ≤ w+4*δ} F hnorm ?_).trans
    (mul_le_mul' le_rfl (measure_mono (fun z hz => hz.trans hW)))
  intro i hi j hj hb
  exact shared_bin_support_collisionND (α i) (α j) (β i) (β j)
    (hle i hi) (hle j hj) (hsupp i hi) (hsupp j hj) hb

end CurrentFalconer
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

noncomputable def pairDistanceLawND (θ : Measure (V × V)) : Measure ℝ :=
  θ.map (fun z => dist z.1 z.2)

instance pairDistanceLawND_finite (θ : Measure (V × V)) [IsFiniteMeasure θ] :
    IsFiniteMeasure (pairDistanceLawND θ) := by unfold pairDistanceLawND; infer_instance

lemma pairDistanceLawND_mono {θ η : Measure (V × V)} (h : θ ≤ η) :
    pairDistanceLawND θ ≤ pairDistanceLawND η :=
  Measure.map_mono h (by fun_prop)

lemma pairDistanceLawND_mass (θ : Measure (V × V)) :
    pairDistanceLawND θ univ=θ univ := by
  rw [pairDistanceLawND,Measure.map_apply (by fun_prop) MeasurableSet.univ,preimage_univ]

lemma pairDistanceLawND_collision (θ η : Measure (V × V))
    [IsFiniteMeasure θ] [IsFiniteMeasure η] (w : ℝ) :
    ((pairDistanceLawND θ).prod (pairDistanceLawND η)) {z : ℝ × ℝ | |z.1-z.2| ≤ w}=
      (θ.prod η) {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} := by
  rw [pairDistanceLawND,pairDistanceLawND,Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (by measurability)]
  rfl

lemma pairDistanceLawND_bin_sq_le (θ η : Measure (V × V))
    [IsFiniteMeasure θ] [IsFiniteMeasure η] (hθη : θ ≤ η) {w : ℝ} (hw : 0<w) :
    (binL2Norm (pairDistanceLawND θ) w)^2 ≤
      (η.prod η) {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} := by
  rw [pow_two,binL2Norm_mul_self]
  apply (real_bin_collision_bound (pairDistanceLawND θ) hw).trans
  rw [pairDistanceLawND_collision]
  exact Measure.prod_mono hθη hθη _

lemma pairDistanceLawND_cell_support (μ : Measure V) [IsFiniteMeasure μ]
    {P Q : Set V} (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (c c' : V) {δ : ℝ} (hPcell : ∀ x ∈ P, dist x c ≤ δ)
    (hQcell : ∀ y ∈ Q, dist y c' ≤ δ) :
    ∀ᵐ r ∂pairDistanceLawND ((μ.restrict P).prod (μ.restrict Q)), |r-dist c c'| ≤ 2*δ := by
  apply (ae_map_iff (by fun_prop) (by measurability)).mpr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hP),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hQ)] with xy hx hy
  have hh := dist_dist_dist_le xy.1 xy.2 c c'
  rw [Real.dist_eq] at hh
  exact hh.trans (by linarith [hPcell xy.1 hx,hQcell xy.2 hy])

variable [InnerProductSpace ℝ V]

theorem suffix_witness_local_binsND (μ : Measure V) [IsFiniteMeasure μ]
    {P Q : Set V} (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (θ : Measure (V × V)) [IsFiniteMeasure θ] (hθ : θ ≤ (μ.restrict P).prod (μ.restrict Q))
    (c c' x₀ y₀ : V) {δ ρ w W : ℝ}
    (hρ : 0<ρ) (hw : 0<w) (hsep : ρ ≤ ‖c-c'‖)
    (hPcell : ∀ x ∈ P, dist x c ≤ δ) (hQcell : ∀ y ∈ Q, dist y c' ≤ δ)
    (hx₀ : x₀ ∈ P) (hy₀ : y₀ ∈ Q) (hxy₀ : x₀ ≠ y₀)
    (htaylor : 2*δ^2/ρ ≤ w) (hwidth : w+8*δ^2/ρ ≤ W) {B : ℝ≥0∞}
    (hproj : ((ProbabilityTheory.cond μ Q).prod (ProbabilityTheory.cond μ Q))
      {z : V × V | |inner ℝ (z.1-z.2) (‖x₀-y₀‖⁻¹ • (x₀-y₀))| ≤ W} ≤ B) :
    (binL2Norm (pairDistanceLawND θ) w)^2 ≤
      ((bandOffsets 3).card:ℝ≥0∞)*B*(μ P*μ Q)^2 := by
  apply (pairDistanceLawND_bin_sq_le θ _ hθ hw).trans
  exact (suffix_witness_local_collisionND μ hP hQ c c' x₀ y₀ hρ hw hsep
    hPcell hQcell hx₀ hy₀ hxy₀ htaylor hwidth hproj).trans_eq (by ring)

end CurrentFalconer
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

lemma treeCell_dist_sqrt {P : CellPath d} {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ treeCell P) (hy : y ∈ treeCell P) :
    dist y x ≤ Real.sqrt (d+1)/(2:ℝ)^P.length := by
  have ht : 0 < (2:ℝ)^P.length := by positivity
  have hcoord (i : Fin d) : |y i-x i| ≤ 1/(2:ℝ)^P.length := by
    rw [abs_le]
    constructor
    · rw [show -(1/(2:ℝ)^P.length)=(-1)/(2:ℝ)^P.length by ring]
      apply (div_le_iff₀ ht).mpr
      have h1 := (hx i).2
      have h2 := (hy i).1
      nlinarith
    · apply (le_div_iff₀ ht).mpr
      have h1 := (hy i).2
      have h2 := (hx i).1
      nlinarith
  have hsq : dist y x^2 ≤ (d:ℝ)*(1/(2:ℝ)^P.length)^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ _ : Fin d, (1/(2:ℝ)^P.length)^2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Real.dist_eq,sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^P.length)).mpr (hcoord i)
      _ = _ := by simp
  apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
  apply hsq.trans
  simp only [div_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ d+1)]
  have hh : (d:ℝ) ≤ d+1 := by linarith
  convert mul_le_mul_of_nonneg_right hh (sq_nonneg (1/(2:ℝ)^P.length)) using 1 <;> ring

lemma classConditional_eq_cond (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (P : CellPath d) :
    classConditional ρ P = ProbabilityTheory.cond ρ (treeCell P) := by
  by_cases hp : ρ (treeCell P)=0
  · simp [classConditional,ProbabilityTheory.cond,hp,Measure.restrict_eq_zero.mpr hp]
  · rw [classConditional,← Measure.coe_nnreal_smul,
      ENNReal.coe_inv (ENNReal.toNNReal_ne_zero.mpr ⟨hp,measure_ne_top ρ _⟩),
      ENNReal.coe_toNNReal (measure_ne_top ρ _)]
    rfl

def CentreSeparated (X Y : CellPath d) (a : ℕ) (K : ℝ) : Prop :=
  K/8/(2:ℝ)^a ≤ dist (treeCenter X) (treeCenter Y) ∧
  dist (treeCenter X) (treeCenter Y) ≤ 4*K/(2:ℝ)^a

lemma separated_parent_points {X Y : CellPath d} {a : ℕ} {K : ℝ}
    (hK : 1000*(d+1:ℝ) < K) (hX : X.length=a) (hY : Y.length=a)
    (hsep : CentreSeparated X Y a K)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ treeCell X) (hy : y ∈ treeCell Y) :
    100*(d+1:ℝ)/(2:ℝ)^a ≤ dist x y := by
  have hx' := ambientGridCell_dist_le (treeCenter_mem X) hx
  have hy' := ambientGridCell_dist_le (treeCenter_mem Y) hy
  change dist x (treeCenter X) ≤ (d+1:ℝ)/(2:ℝ)^X.length at hx'
  change dist y (treeCenter Y) ≤ (d+1:ℝ)/(2:ℝ)^Y.length at hy'
  rw [hX] at hx'
  rw [hY] at hy'
  have hh := dist_triangle4 (treeCenter X) x y (treeCenter Y)
  rw [dist_comm (treeCenter X) x] at hh
  have hb : 125*(d+1:ℝ)/(2:ℝ)^a ≤ K/8/(2:ℝ)^a := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hn : 0 ≤ (d+1:ℝ)/(2:ℝ)^a := by positivity
  have hs := hb.trans hsep.1
  simp only [div_eq_mul_inv] at hx' hy' hn hs ⊢
  nlinarith

lemma suffix_dyadic_ratio {a p t : ℕ} (h : a+t ≤ 2*p) :
    (2:ℝ)^a/((2:ℝ)^p)^2 ≤ 1/(2:ℝ)^t := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul,← pow_add,← pow_mul,Nat.mul_comm p 2]
  exact pow_le_pow_right₀ (by norm_num) h

lemma suffix_taylor_widths {a p t J i N : ℕ} {sig : ℝ}
    (h : a+t ≤ 2*p) (hJ : 0 < J) (hi : i ≤ J)
    (hR : 2 ≤ ((2:ℝ)^N)^(500*sig)) :
    2*(Real.sqrt (d+1)/(2:ℝ)^p)^2/(100*(d+1:ℝ)/(2:ℝ)^a) ≤ (2:ℝ)^(-(t:ℝ)) ∧
    (2:ℝ)^(-(t:ℝ))+8*(Real.sqrt (d+1)/(2:ℝ)^p)^2/(100*(d+1:ℝ)/(2:ℝ)^a) ≤
      testWidth N J i t sig := by
  have hd : (d+1:ℝ) ≠ 0 := by positivity
  have hid : (Real.sqrt (d+1)/(2:ℝ)^p)^2/(100*(d+1:ℝ)/(2:ℝ)^a) =
      (1/100:ℝ)*((2:ℝ)^a/((2:ℝ)^p)^2) := by
    rw [div_pow,Real.sq_sqrt (by positivity)]
    field_simp
  have hratio := suffix_dyadic_ratio h
  have hw : (2:ℝ)^(-(t:ℝ)) = 1/(2:ℝ)^t := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  have hfirst : (i:ℝ)/J ≤ 1 := (div_le_one (by exact_mod_cast hJ)).mpr (by exact_mod_cast hi)
  have hw0 : 0 ≤ (2:ℝ)^(-(t:ℝ)) := by positivity
  have hsmall : (Real.sqrt (d+1)/(2:ℝ)^p)^2/(100*(d+1:ℝ)/(2:ℝ)^a) ≤
      (1/100:ℝ)*(2:ℝ)^(-(t:ℝ)) := by rw [hid,hw]; linarith
  have hwide : 2*(2:ℝ)^(-(t:ℝ)) ≤ testWidth N J i t sig := by
    unfold testWidth
    have hprod : 2 ≤ (2-(i:ℝ)/J)*((2:ℝ)^N)^(500*sig) :=
      hR.trans (le_mul_of_one_le_left (by positivity) (by linarith))
    nlinarith [mul_le_mul_of_nonneg_right hprod hw0]
  simp only [div_eq_mul_inv] at hsmall ⊢
  constructor <;> nlinarith

lemma source_suffix_projection_mem (A : ℕ → ℝ) {N q a t : ℕ}
    (ht : t ≤ N) (hw : a+100*q < t)
    (hs : a+t < 2*policyDepth A N q a t) :
    PolicyDescriptor.projection (policyDepth A N q a t) t ∈
      policyDescriptorList A N q a t := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,t),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      le_rfl,le_rfl,hw⟩
  · apply Finset.mem_union_right
    simp [hs]

namespace PositiveDistanceState
variable (e : PositiveDistanceState d)
noncomputable def atCells (P Q : CellPath d) : PositiveDistanceState d := {e with X := P,Y := Q}

theorem uniform_actual_suffix_local_bins {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ e : PositiveDistanceState d, e.sig=sig → N₀ ≤ e.N →
      ∀ K : ℝ, 1000*(d+1:ℝ)<K → CentreSeparated e.X e.Y e.a K →
      e.X.length=e.a → e.Y.length=e.a → IsFiniteMeasure e.ρ →
      0 < e.J → e.i ≤ e.J → 0 < e.q → e.t ≤ e.N → e.a+100*e.q<e.t →
      let A := adjustedProfile (d := d) e.mass e.N
      let p := policyDepth A e.N e.q e.a e.t
      e.a+e.t < 2*p →
      ∀ P Q : CellPath d, P.length=p → Q.length=p →
      P.take e.a=e.X → Q.take e.a=e.Y →
      ∀ x ∈ treeCell P, ∀ y ∈ treeCell Q, (x,y) ∈ e.good →
      (binL2Norm (e.atCells P Q).distance e.width)^2 ≤
        ((bandOffsets 3).card:ℝ≥0∞)*ENNReal.ofReal ((2:ℝ)^(-((e.t:ℝ)-p))*
          ((2:ℝ)^e.N)^(A p-intervalMin A p e.t+e.C*sig)) *
          (e.ρ (treeCell P)*e.ρ (treeCell Q))^2 := by
  obtain ⟨N₀,h₀⟩ := fixed_constant_absorbed (mul_pos (by norm_num : (0:ℝ)<500) hsig) 2
  refine ⟨N₀,?_⟩
  intro e he hN K hK hsep hX hY hf hJ hi hq ht hw A p hs P Q hP hQ hPX hQY x hx y hy hg
  let finiteSourceMeasure := hf
  have hpdesc := source_suffix_projection_mem A ht hw hs
  have htest := (hg (.projection p e.t) hpdesc).2 Q ((mem_dyadicPaths _ _).mpr hQ) hy
  change ‖radialVector x y‖=1 ∧ _ at htest
  have hproj : ((ProbabilityTheory.cond e.ρ (treeCell Q)).prod (ProbabilityTheory.cond e.ρ (treeCell Q)))
      {z | |inner ℝ (z.1-z.2) (‖x-y‖⁻¹ • (x-y))| ≤ testWidth e.N e.J e.i e.t e.sig} ≤
        ENNReal.ofReal ((2:ℝ)^(-((e.t:ℝ)-p))*
          ((2:ℝ)^e.N)^(A p-intervalMin A p e.t+e.C*sig)) := by
    simpa only [fullProjectionCollision,classConditional_eq_cond,radialVector,he] using htest.2
  have hPx : treeCell P ⊆ treeCell e.X := by simpa only [hPX] using treeCell_subset_take P e.a
  have hQy : treeCell Q ⊆ treeCell e.Y := by simpa only [hQY] using treeCell_subset_take Q e.a
  have hrho : 0 < 100*(d+1:ℝ)/(2:ℝ)^e.a := by positivity
  have hxy := separated_parent_points hK hX hY hsep (hPx hx) (hQy hy)
  have hxy' : x ≠ y := by
    intro heq
    subst y
    simp only [dist_self] at hxy
    linarith
  have hcent := separated_parent_points hK hX hY hsep (hPx (treeCenter_mem P)) (hQy (treeCenter_mem Q))
  rw [dist_eq_norm] at hcent
  have hwidths := suffix_taylor_widths (d := d) (le_of_lt hs) hJ hi
    (show 2 ≤ ((2:ℝ)^e.N)^(500*e.sig) by rw [he]; exact h₀ _ hN)
  have hPc (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ treeCell P) :
      dist z (treeCenter P) ≤ Real.sqrt (d+1)/(2:ℝ)^p := by
    simpa only [hP] using treeCell_dist_sqrt (treeCenter_mem P) hz
  have hQc (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ treeCell Q) :
      dist z (treeCenter Q) ≤ Real.sqrt (d+1)/(2:ℝ)^p := by
    simpa only [hQ] using treeCell_dist_sqrt (treeCenter_mem Q) hz
  have finiteCellMeasure : IsFiniteMeasure (e.atCells P Q).ρ := hf
  exact suffix_witness_local_binsND e.ρ (measurableSet_treeCell P) (measurableSet_treeCell Q)
    (e.atCells P Q).pair (Measure.restrict_le_self)
    (treeCenter P) (treeCenter Q) x y hrho (by positivity) hcent
    hPc hQc hx hy hxy' hwidths.1 hwidths.2 hproj

end PositiveDistanceState

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
