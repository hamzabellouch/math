import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.MinimalDescriptorLength
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.SharedBinSupportCollision

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

noncomputable def nominalRadius (N : ℕ) (sig : ℝ) (l : ℕ) : ℝ :=
  min 1 (1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig))

lemma testWidth_gap (N : ℕ) (sig : ℝ) {J : ℕ} (hJ : 0<J) (i n : ℕ) :
    testWidth N J i n sig-testWidth N J (i+1) n sig =
      ((2:ℝ)^N)^(500*sig)/((J:ℝ)*(2:ℝ)^n) := by
  have hj : (J:ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  simp only [testWidth,Nat.cast_add,Nat.cast_one,Real.rpow_neg (by norm_num : (0:ℝ)≤2),
    Real.rpow_natCast]
  field_simp
  ring

lemma uniform_testWidth_gap {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J)
    (C : ℝ) (hC : 0≤C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g n : ℕ, g≤n → ∀ i : ℕ,
      testWidth N J (i+1) n sig + (C/(2:ℝ)^g)*nominalRadius N sig (n-g) ≤
        testWidth N J i n sig := by
  obtain ⟨N₀,h₀⟩ := fixed_constant_absorbed (by positivity : 0<450*sig) (C*J)
  refine ⟨N₀,?_⟩
  intro N hN g n hgn i
  have hj : 0<(J:ℝ) := by exact_mod_cast hJ
  have hRp : 0<(2:ℝ)^N := by positivity
  have hc := mul_le_mul_of_nonneg_right (h₀ N hN)
    (by positivity : 0≤((2:ℝ)^N)^(50*sig))
  have he : ((2:ℝ)^N)^(450*sig)*((2:ℝ)^N)^(50*sig)=((2:ℝ)^N)^(500*sig) := by
    rw [← Real.rpow_add hRp]; congr 1; ring
  rw [he] at hc
  have hp : (2:ℝ)^g*(2:ℝ)^(n-g)=(2:ℝ)^n := by rw [← pow_add,Nat.add_sub_of_le hgn]
  have hb : (C/(2:ℝ)^g)*nominalRadius N sig (n-g) ≤
      ((2:ℝ)^N)^(500*sig)/((J:ℝ)*(2:ℝ)^n) := by
    calc
      _ ≤ (C/(2:ℝ)^g)*(1/(2:ℝ)^(n-g)*((2:ℝ)^N)^(50*sig)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = (C*(J:ℝ)*((2:ℝ)^N)^(50*sig))/((J:ℝ)*(2:ℝ)^n) := by
        rw [← hp]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)
  rw [← testWidth_gap N sig hJ i n] at hb
  linarith

lemma fullParallelCount_transfer (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (g p : ℕ) (P : CellPath d) {W W' ε : ℝ} {v w : EuclideanSpace ℝ (Fin d)}
    (hv : ‖v‖=1) (hw : ‖w‖=1) (hd : dist v w ≤ ε)
    (hW : W'+(20*(d+1:ℝ)/(2:ℝ)^g)*ε ≤ W) :
    fullParallelCount ρ g p P W' w ≤ fullParallelCount ρ g p P W v := by
  apply Finset.card_le_card
  intro Q hQ
  obtain ⟨hQ,hpos,hr,hperp⟩ := Finset.mem_filter.mp hQ
  refine Finset.mem_filter.mpr ⟨hQ,hpos,hr,?_⟩
  have hε : 0≤ε := dist_nonneg.trans hd
  have hchange := graphPerpND_change_direction w v (treeCenter Q-treeCenter P) hw hv
  have hnorm : ‖graphPerpND v (treeCenter Q-treeCenter P)‖ ≤
      ‖graphPerpND w (treeCenter Q-treeCenter P)‖+
        2*‖treeCenter Q-treeCenter P‖*dist v w := by
    rw [dist_comm w v] at hchange
    exact (norm_le_norm_sub_add _ _).trans (by linarith)
  have hr' : ‖treeCenter Q-treeCenter P‖ ≤ 10*(d+1:ℝ)/(2:ℝ)^g := by
    simpa only [dist_eq_norm] using hr.le
  have htotal := mul_le_mul (mul_le_mul_of_nonneg_left hr' (by norm_num : (0:ℝ)≤2)) hd
    dist_nonneg (by positivity : 0≤2*(10*(d+1:ℝ)/(2:ℝ)^g))
  simp only [div_eq_mul_inv] at htotal hW
  nlinarith

lemma classConditional_ae_mem (ρ : Measure (EuclideanSpace ℝ (Fin d))) (P : CellPath d) :
    ∀ᵐ x ∂classConditional ρ P, x ∈ treeCell P :=
  Measure.ae_smul_measure (ae_restrict_mem (measurableSet_treeCell P)) _

lemma fullProjectionCollision_transfer (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (P : CellPath d) {W W' ε : ℝ} {v w : EuclideanSpace ℝ (Fin d)}
    (hd : dist v w ≤ ε)
    (hW : W'+((d+1:ℝ)/(2:ℝ)^P.length)*ε ≤ W) :
    fullProjectionCollision ρ P W' w ≤ fullProjectionCollision ρ P W v := by
  apply measure_mono_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (classConditional_ae_mem ρ P),
    Measure.quasiMeasurePreserving_snd.ae (classConditional_ae_mem ρ P)] with z hz hz'
  intro hproj
  change |inner ℝ (z.1-z.2) w| ≤ W' at hproj
  have hdiam : ‖z.1-z.2‖ ≤ (d+1:ℝ)/(2:ℝ)^P.length := by
    simpa only [dist_eq_norm] using ambientGridCell_dist_le hz' hz
  have hn : ‖v-w‖ ≤ ε := by simpa only [dist_eq_norm] using hd
  have hb := abs_real_inner_le_norm (z.1-z.2) (v-w)
  rw [inner_sub_right] at hb
  have hb' := hb.trans (mul_le_mul hdiam hn (norm_nonneg _) (by positivity))
  have ht := abs_add_le (inner ℝ (z.1-z.2) v-inner ℝ (z.1-z.2) w)
    (inner ℝ (z.1-z.2) w)
  simp only [sub_add_cancel] at ht
  exact ht.trans (by linarith)

def ValidDescriptor (N : ℕ) : PolicyDescriptor → Prop
  | .parallel g p => g ≤ p ∧ p ≤ N
  | .projection p t => p ≤ t ∧ t ≤ N

lemma policyDescriptor_valid (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N)
    {b : PolicyDescriptor} (hb : b ∈ policyDescriptorList A N q a t) : ValidDescriptor N b := by
  obtain ⟨s,u,_,hut,_,_,hpos,_,hbound⟩ := policyDescriptor_origin A hq hb
  cases b <;> simp only [descriptorLength,descriptorAnchor,ValidDescriptor] at * <;> omega

lemma policyDescriptor_anchor_le_end (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {b : PolicyDescriptor} (hb : b ∈ policyDescriptorList A N q a t) :
    descriptorAnchor b ≤ t := by
  obtain ⟨_,u,_,hut,_,_,_,_,hu⟩ := policyDescriptor_origin A hq hb
  omega

lemma uniform_descriptorGood_transfer {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ρ →
      ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ) (b : PolicyDescriptor), ValidDescriptor N b →
      ∀ P : CellPath d, P.length=descriptorAnchor b →
      ∀ v w : EuclideanSpace ℝ (Fin d), ‖w‖=1 →
      dist v w ≤ nominalRadius N sig (descriptorLength b) →
      v ∈ descriptorGood ρ m N sig C J i P b →
      w ∈ descriptorGood ρ m N sig C J (i+1) P b := by
  obtain ⟨N₁,h₁⟩ := uniform_testWidth_gap hsig hJ (20*(d+1)) (by positivity)
  obtain ⟨N₂,h₂⟩ := uniform_testWidth_gap hsig hJ (d+1) (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ρ hf m C i b hb P hP v w hw hd hg
  have := hf
  cases b with
  | parallel g p =>
    exact ⟨hw,(Nat.cast_le.mpr (fullParallelCount_transfer ρ g p P hg.1 hw hd
      (h₁ N ((le_max_left _ _).trans hN) g p hb.1 i))).trans hg.2⟩
  | projection p t =>
    apply And.intro hw
    apply (fullProjectionCollision_transfer ρ P hd ?_).trans hg.2
    simp only [descriptorAnchor] at hP
    rw [hP]
    exact h₂ N ((le_max_right _ _).trans hN) p t hb.1 i

lemma dyadic_ratio_nominal {a p l N : ℕ} {sig : ℝ} (hsig : 0 ≤ sig) (hl : a+l≤p) :
    (2:ℝ)^a/(2:ℝ)^p ≤ nominalRadius N sig l := by
  have hb : (2:ℝ)^a/(2:ℝ)^p ≤ 1/(2:ℝ)^l := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul,← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hl
  have hR : 1 ≤ ((2:ℝ)^N)^(50*sig) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
  apply le_min
  · exact (div_le_one (by positivity)).mpr (pow_le_pow_right₀ (by norm_num) (by omega))
  · exact hb.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hR (by positivity : 0≤1/(2:ℝ)^l))

lemma same_tree_ancestor {P A : CellPath d} {a p : ℕ} (hP : P.length=p)
    (hA : A.length=a) (hap : a≤p) {x x' : EuclideanSpace ℝ (Fin d)}
    (hxA : x ∈ treeCell A) (hx : x ∈ treeCell P) (hx' : x' ∈ treeCell P) :
    x' ∈ treeCell A := by
  have hlen : (P.take a).length=A.length := by simp [List.length_take,hP,hA,hap]
  have he : P.take a=A := by
    by_contra hn
    exact Set.disjoint_left.mp (treeCell_disjoint hlen hn) (treeCell_subset_take _ _ hx) hxA
  simpa only [he] using treeCell_subset_take P a hx'

lemma fine_radial_dist {X Y P Q : CellPath d} {a p : ℕ} {K : ℝ}
    (hK : 1000*(d+1:ℝ)<K) (hX : X.length=a) (hY : Y.length=a)
    (hsep : CentreSeparated X Y a K) (hP : P.length=p) (hQ : Q.length=p)
    (hPX : P.take a=X) (hQY : Q.take a=Y)
    {x y x' y' : EuclideanSpace ℝ (Fin d)} (hx : x ∈ treeCell P) (hy : y ∈ treeCell Q)
    (hx' : x' ∈ treeCell P) (hy' : y' ∈ treeCell Q) :
    dist (radialVector x y) (radialVector x' y') ≤ (2:ℝ)^a/(2:ℝ)^p := by
  have hPx : treeCell P ⊆ treeCell X := by simpa only [hPX] using treeCell_subset_take P a
  have hQy : treeCell Q ⊆ treeCell Y := by simpa only [hQY] using treeCell_subset_take Q a
  have hd := separated_parent_points hK hX hY hsep (hPx hx) (hQy hy)
  have hd' := separated_parent_points hK hX hY hsep (hPx hx') (hQy hy')
  have hpos : 0<100*(d+1:ℝ)/(2:ℝ)^a := by positivity
  rw [dist_eq_norm] at hd hd'
  have hmove : ‖(x-y)-(x'-y')‖ ≤ 2*(d+1:ℝ)/(2:ℝ)^p := by
    have he : (x-y)-(x'-y')=(x-x')-(y-y') := by abel
    rw [he]
    have hxmove := ambientGridCell_dist_le hx' hx
    have hymove := ambientGridCell_dist_le hy' hy
    change dist x x' ≤ (d+1:ℝ)/(2:ℝ)^P.length at hxmove
    change dist y y' ≤ (d+1:ℝ)/(2:ℝ)^Q.length at hymove
    rw [hP,dist_eq_norm] at hxmove
    rw [hQ,dist_eq_norm] at hymove
    exact (norm_sub_le _ _).trans (by simp only [div_eq_mul_inv] at hxmove hymove ⊢; linarith)
  apply (normalized_direction_distND (x-y) (x'-y') (hpos.trans_le hd) (hpos.trans_le hd')).trans
  apply (div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hmove (by norm_num : (0:ℝ) ≤ 2)) hpos hd).trans
  have he : 2*(2*(d+1:ℝ)/(2:ℝ)^p)/(100*(d+1:ℝ)/(2:ℝ)^a) =
      (1/25:ℝ)*((2:ℝ)^a/(2:ℝ)^p) := by
    field_simp
    ring_nf
  rw [he]
  have hg : 0≤(2:ℝ)^a/(2:ℝ)^p := by positivity
  linarith

namespace PositiveDistanceState
lemma uniform_suffix_good_transport {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ e : PositiveDistanceState d, e.sig=sig → e.J=J → N₀≤e.N →
      IsFiniteMeasure e.ρ → ∀ K : ℝ, 1000*(d+1:ℝ)<K → CentreSeparated e.X e.Y e.a K →
      e.X.length=e.a → e.Y.length=e.a → 0<e.q →
      ∀ p : ℕ, e.a≤p → p≤e.t → e.t≤e.N →
      ∀ P Q : CellPath d, P.length=p → Q.length=p → P.take e.a=e.X → Q.take e.a=e.Y →
      ∀ x ∈ treeCell P, ∀ y ∈ treeCell Q, (x,y) ∈ e.good →
      ∀ x' ∈ treeCell P, ∀ y' ∈ treeCell Q,
      (x',y') ∈ ({e with t := p,i := e.i+1} : PositiveDistanceState d).good := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorGood_transfer (d := d) hsig hJ
  refine ⟨N₀,?_⟩
  intro e hsig' hJ' hN hf K hK hsep hX hY hq p hap hpt htN P Q hP hQ hPX hQY x hx y hy hg x' hx' y' hy'
  have hmove := fine_radial_dist hK hX hY hsep hP hQ hPX hQY hx hy hx' hy'
  have hPx : treeCell P ⊆ treeCell e.X := by simpa only [hPX] using treeCell_subset_take P e.a
  have hQy : treeCell Q ⊆ treeCell e.Y := by simpa only [hQY] using treeCell_subset_take Q e.a
  have hne : x' ≠ y' := by
    have hh := separated_parent_points hK hX hY hsep (hPx hx') (hQy hy')
    exact dist_pos.mp ((by positivity : 0<100*(d+1:ℝ)/(2:ℝ)^e.a).trans_le hh)
  intro b hb
  change b ∈ policyDescriptorList (adjustedProfile (d := d) e.mass e.N) e.N e.q e.a p at hb
  have hb' := policyDescriptorList_mono (adjustedProfile (d := d) e.mass e.N) le_rfl hpt hb
  have hbg := hg b hb'
  have ha := policyDescriptor_anchor_le_end (adjustedProfile (d := d) e.mass e.N) hq hb
  have hl := policyDescriptor_twice_length (adjustedProfile (d := d) e.mass e.N) hq hb
  have hv := policyDescriptor_valid (adjustedProfile (d := d) e.mass e.N) hq (hpt.trans htN) hb
  have hrad := hmove.trans (dyadic_ratio_nominal (N := e.N) hsig.le (by omega : e.a+descriptorLength b≤p))
  have htransfer (A : CellPath d) (hA : A.length=descriptorAnchor b)
      (hw : radialVector x y ∈ descriptorGood e.ρ e.mass e.N e.sig e.C e.J e.i A b) :
      radialVector x' y' ∈ descriptorGood e.ρ e.mass e.N e.sig e.C e.J (e.i+1) A b := by
    rw [hsig',hJ'] at hw ⊢
    exact h₀ e.N hN e.ρ hf e.mass e.C e.i b hv A hA _ _ (norm_radialVector hne) hrad hw
  constructor
  · intro A hA hxA
    have hlen := (mem_dyadicPaths _ _).mp hA
    apply htransfer A hlen
    apply hbg.1 A hA
    exact same_tree_ancestor hP hlen ha hxA hx' hx
  · intro A hA hyA
    have hlen := (mem_dyadicPaths _ _).mp hA
    apply htransfer A hlen
    apply hbg.2 A hA
    exact same_tree_ancestor hQ hlen ha hyA hy' hy
end PositiveDistanceState

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Filter Real
open scoped Topology

noncomputable def sourceMaskScaleND (l : ℕ) (R σ : ℝ) : ℝ :=
  max 1 ((2:ℝ)^l*R^(-50*σ))

noncomputable def sourceMaskRadiusND (d l : ℕ) (R σ : ℝ) : ℝ :=
  (sourceMaskScaleND l R σ)⁻¹/(100*(d+1)^2)

noncomputable def sourceTestWidthND (J i n : ℕ) (R σ : ℝ) : ℝ :=
  (2-(i:ℝ)/J)*((2:ℝ)^n)⁻¹*R^(500*σ)

lemma sourceMaskScaleND_one_le (l : ℕ) (R σ : ℝ) : 1 ≤ sourceMaskScaleND l R σ := le_max_left _ _

lemma sourceMaskScaleND_pos (l : ℕ) (R σ : ℝ) : 0<sourceMaskScaleND l R σ :=
  zero_lt_one.trans_le (sourceMaskScaleND_one_le l R σ)

lemma sourceMaskRadiusND_pos (d l : ℕ) (R σ : ℝ) : 0<sourceMaskRadiusND d l R σ :=
  div_pos (inv_pos.mpr (sourceMaskScaleND_pos l R σ)) (by positivity)

lemma sourceMaskScaleND_mono {l L : ℕ} (h : l ≤ L) {R σ : ℝ} (hR : 0 ≤ R) :
    sourceMaskScaleND l R σ ≤ sourceMaskScaleND L R σ := by
  apply max_le_max_left
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h) (Real.rpow_nonneg hR _)

lemma sourceMaskScaleND_inv_depth {g p : ℕ} (hgp : g ≤ p) {R σ : ℝ} (hR : 0<R) :
    ((2:ℝ)^g)⁻¹*(sourceMaskScaleND (p-g) R σ)⁻¹ ≤ ((2:ℝ)^p)⁻¹*R^(50*σ) := by
  have hpos : 0<(2:ℝ)^(p-g)*R^(-50*σ) := by positivity
  have hh := inv_anti₀ hpos (le_max_right (1:ℝ) ((2:ℝ)^(p-g)*R^(-50*σ)))
  apply (mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ ((2:ℝ)^g)⁻¹)).trans_eq
  rw [mul_inv_rev,show -50*σ=-(50*σ) by ring,Real.rpow_neg hR.le,inv_inv]
  calc
    _ = (((2:ℝ)^g)*((2:ℝ)^(p-g)))⁻¹*R^(50*σ) := by rw [mul_inv_rev]; ring
    _ = _ := by rw [← pow_add,Nat.add_sub_of_le hgp]

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
