import Mathlib
import OAI.Probability.LatticeSurface.Convexity.RadialExposure
import OAI.Probability.LatticeSurface.Geometry.BlockVolume
import OAI.Probability.LatticeSurface.Geometry.FacetExposure
import OAI.Probability.LatticeSurface.Geometry.TriangularCover
import OAI.Probability.LatticeSurface.Geometry.TriangularGeometry

namespace OAI

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

end TriangularLipschitz

namespace FacetExposure

end FacetExposure

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

lemma shell_eq_box_not_interior {L : ℕ} {x : Vertex} :
    x ∈ shell L ↔ x ∈ box L ∧ x ∉ interior L := Finset.mem_sdiff

lemma latticeDist_box_le {L : ℕ} {x y : Vertex} (hx : x ∈ box L) (hy : y ∈ box L) :
    latticeDist x y ≤ 2*(L:ℝ) := by
  obtain ⟨⟨hx0,hxL⟩,⟨hx20,hx2L⟩⟩ := mem_box.mp hx
  obtain ⟨⟨hy0,hyL⟩,⟨hy20,hy2L⟩⟩ := mem_box.mp hy
  have hx' : 0 ≤ (x.1:ℝ) ∧ (x.1:ℝ) ≤ L := by exact_mod_cast And.intro hx0 hxL
  have hx2' : 0 ≤ (x.2:ℝ) ∧ (x.2:ℝ) ≤ L := by exact_mod_cast And.intro hx20 hx2L
  have hy' : 0 ≤ (y.1:ℝ) ∧ (y.1:ℝ) ≤ L := by exact_mod_cast And.intro hy0 hyL
  have hy2' : 0 ≤ (y.2:ℝ) ∧ (y.2:ℝ) ≤ L := by exact_mod_cast And.intro hy20 hy2L
  simp only [latticeDist, max_le_iff, abs_le]
  constructor
  · constructor <;> constructor <;> linarith
  · constructor <;> linarith

lemma endpoint_shell_difference {L : ℕ} {h χ : Vertex → ℝ}
    (hplus : 0 < fillingVolume L (fun x => h x+χ x))
    (hminus : 0 < fillingVolume L (fun x => h x-χ x))
    {b c : Vertex} (hb : b ∈ shell L) (hc : c ∈ shell L) :
    |χ b-χ c| ≤ latticeDist b c := by
  obtain ⟨ap,hap⟩ : (fillingPolytope L (fun x => h x+χ x)).Nonempty :=
    nonempty_of_measure_ne_zero hplus.ne'
  obtain ⟨am,ham⟩ : (fillingPolytope L (fun x => h x-χ x)).Nonempty :=
    nonempty_of_measure_ne_zero hminus.ne'
  rw [shell_eq_box_not_interior] at hb hc
  have hp := near_global_bound hap hb.1 hc.1
  have hm := near_global_bound ham hb.1 hc.1
  simp only [filledHeight_fixed _ _ _ hb.2, filledHeight_fixed _ _ _ hc.2, one_mul] at hp hm
  obtain ⟨hp₁,hp₂⟩ := abs_le.mp hp
  obtain ⟨hm₁,hm₂⟩ := abs_le.mp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma filledHeight_constant_shift (L : ℕ) (g : Vertex → ℝ) (r : ℝ) (x : Vertex) :
    filledHeight L (fun z => g z+r) (fun z => g z+r) x = g x+r := by
  apply filledHeight_center

lemma filledHeight_base_difference {L : ℕ} {s g : Vertex → ℝ} {r η : ℝ} (hη : 0 ≤ η)
    (hs : ∀ b ∈ shell L, |s b-(g b+r)| ≤ η) {x : Vertex} (hx : x ∈ box L) :
    |filledHeight L s (fun z => g z+r) x-(g x+r)| ≤ η := by
  by_cases hi : x ∈ interior L
  · simp only [filledHeight, dite_eq_left hi, sub_self, abs_zero]
    exact hη
  · rw [filledHeight_fixed _ _ _ hi]
    exact hs x (shell_eq_box_not_interior.mpr ⟨hx,hi⟩)

lemma filledHeight_change_bound {L : ℕ} {s : Vertex → ℝ} (a a₀ : Filling L) (x : Vertex) :
    |filledHeight L s a x-filledHeight L s a₀ x| ≤ ‖a-a₀‖ := by
  by_cases hi : x ∈ interior L
  · simp only [filledHeight, dite_eq_left hi]
    exact norm_le_pi_norm (a-a₀) ⟨x,hi⟩
  · simp only [filledHeight_fixed _ _ _ hi, sub_self, abs_zero]
    exact norm_nonneg _

lemma filledHeight_edge_change_bound {L : ℕ} {s : Vertex → ℝ} (a a₀ : Filling L) (x y : Vertex) :
    |(filledHeight L s a x-filledHeight L s a y)-
      (filledHeight L s a₀ x-filledHeight L s a₀ y)| ≤ 2*‖a-a₀‖ := by
  calc
    _ = |(filledHeight L s a x-filledHeight L s a₀ x)-
      (filledHeight L s a y-filledHeight L s a₀ y)| := by congr 1; ring
    _ ≤ |filledHeight L s a x-filledHeight L s a₀ x|+
      |filledHeight L s a y-filledHeight L s a₀ y| := abs_sub _ _
    _ ≤ ‖a-a₀‖+‖a-a₀‖ := add_le_add (filledHeight_change_bound a a₀ x) (filledHeight_change_bound a a₀ y)
    _ = 2*‖a-a₀‖ := by ring

lemma shifted_exposure {L : ℕ} {g s : Vertex → ℝ} {x y : Vertex} {β r : ℝ}
    (hβ : 0 < β)
    (hs : ∀ b ∈ shell L, |s b-(g b+r)| ≤ β/4)
    (hex : ∀ v ∈ box L, ∀ w ∈ box L, Adj v w → s(v,w) ≠ s(x,y) → |g v-g w| ≤ 1-β) :
    ∀ v ∈ box L, ∀ w ∈ box L, Adj v w → s(v,w) ≠ s(x,y) →
      |filledHeight L s (fun z => g z+r) v-filledHeight L s (fun z => g z+r) w| ≤ 1-β/2 := by
  intro v hv w hw hvw hne
  have hgv := filledHeight_base_difference (by linarith : 0 ≤ β/4) hs hv
  have hgw := filledHeight_base_difference (by linarith : 0 ≤ β/4) hs hw
  have hbase : |(g v+r)-(g w+r)| ≤ 1-β := by simpa only [add_sub_add_right_eq_sub] using hex v hv w hw hvw hne
  have htri := abs_add_le (filledHeight L s (fun z => g z+r) v-(g v+r))
    (((g v+r)-(g w+r))+((g w+r)-filledHeight L s (fun z => g z+r) w))
  have htri₂ := abs_add_le ((g v+r)-(g w+r)) ((g w+r)-filledHeight L s (fun z => g z+r) w)
  rw [abs_sub_comm (g w+r)] at htri₂
  have heq : filledHeight L s (fun z => g z+r) v-(g v+r)+
      ((g v+r-(g w+r))+(g w+r-filledHeight L s (fun z => g z+r) w)) =
      filledHeight L s (fun z => g z+r) v-filledHeight L s (fun z => g z+r) w := by ring
  rw [heq] at htri
  linarith

lemma filling_of_small_perturbation_on_facet {L : ℕ} {s : Vertex → ℝ} {x y : Vertex}
    {a a₀ : Filling L} {β : ℝ}
    (hfacet : |filledHeight L s a x-filledHeight L s a y| ≤ 1)
    (hother : ∀ v ∈ box L, ∀ w ∈ box L, Adj v w → s(v,w) ≠ s(x,y) →
      |filledHeight L s a₀ v-filledHeight L s a₀ w| ≤ 1-β)
    (hsmall : 2*‖a-a₀‖ ≤ β) : a ∈ fillingPolytope L s := by
  intro v hv w hw hvw
  by_cases he : s(v,w)=s(x,y)
  · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hfacet
    · simpa only [abs_sub_comm] using hfacet
  · have hdiff := filledHeight_edge_change_bound (s:=s) a a₀ v w
    have h₀ := hother v hv w hw hvw he
    have htri := abs_add_le ((filledHeight L s a v-filledHeight L s a w)-
      (filledHeight L s a₀ v-filledHeight L s a₀ w))
      (filledHeight L s a₀ v-filledHeight L s a₀ w)
    rw [sub_add_cancel] at htri
    linarith

end TriangularLipschitz

namespace TriangularLipschitz

lemma ball_subset_polytope_of_slack {L : ℕ} {s : Vertex → ℝ} {a₀ : Filling L} {δ : ℝ}
    (hh : ∀ x ∈ box L, ∀ y ∈ box L, Adj x y →
      |filledHeight L s a₀ x-filledHeight L s a₀ y| ≤ 1-δ) :
    Metric.ball a₀ (δ/4) ⊆ fillingPolytope L s := by
  intro a ha x hx y hy hxy
  have hnorm : ‖a-a₀‖ < δ/4 := by simpa only [Metric.mem_ball, dist_eq_norm] using ha
  have hdiff := filledHeight_edge_change_bound (s:=s) a a₀ x y
  have htri := abs_add_le ((filledHeight L s a x-filledHeight L s a y)-
    (filledHeight L s a₀ x-filledHeight L s a₀ y))
    (filledHeight L s a₀ x-filledHeight L s a₀ y)
  rw [sub_add_cancel] at htri
  have h := hh x hx y hy hxy
  linarith [norm_nonneg (a-a₀)]

lemma fillingVolume_pos_of_slack {L : ℕ} {s : Vertex → ℝ} {a₀ : Filling L} {δ : ℝ}
    (hδ : 0 < δ)
    (hh : ∀ x ∈ box L, ∀ y ∈ box L, Adj x y →
      |filledHeight L s a₀ x-filledHeight L s a₀ y| ≤ 1-δ) :
    0 < fillingVolume L s :=
  (Metric.measure_ball_pos volume a₀ (by linarith : 0 < δ/4)).trans_le
    (measure_mono (ball_subset_polytope_of_slack hh))

lemma filledHeight_mix (L : ℕ) (s t : Vertex → ℝ) (a b : Filling L) (α γ : ℝ) (x : Vertex) :
    filledHeight L (fun x => α*s x+γ*t x) (α • a+γ • b) x =
      α*filledHeight L s a x+γ*filledHeight L t b x := by
  unfold filledHeight
  split_ifs <;> rfl

lemma fillingPolytope_mix {L : ℕ} {s t : Vertex → ℝ} {a b : Filling L}
    {α γ : ℝ} (ha : a ∈ fillingPolytope L s) (hb : b ∈ fillingPolytope L t)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hsum : α+γ=1) :
    α • a+γ • b ∈ fillingPolytope L (fun x => α*s x+γ*t x) := by
  intro x hx y hy hxy
  rw [filledHeight_mix, filledHeight_mix]
  calc
    _ = |α*(filledHeight L s a x-filledHeight L s a y)+
      γ*(filledHeight L t b x-filledHeight L t b y)| := by congr 1; ring
    _ ≤ |α*(filledHeight L s a x-filledHeight L s a y)|+
      |γ*(filledHeight L t b x-filledHeight L t b y)| := abs_add_le _ _
    _ = α*|filledHeight L s a x-filledHeight L s a y|+
      γ*|filledHeight L t b x-filledHeight L t b y| := by rw [abs_mul,abs_mul,abs_of_nonneg hα,abs_of_nonneg hγ]
    _ ≤ α*1+γ*1 := add_le_add (mul_le_mul_of_nonneg_left (ha x hx y hy hxy) hα)
      (mul_le_mul_of_nonneg_left (hb x hx y hy hxy) hγ)
    _ = 1 := by linarith

lemma fillingVolume_interpolated_pos {L : ℕ} {h t : Vertex → ℝ} {δ α : ℝ}
    (hδ : 0 < δ) (hα : 0 ≤ α) (hα1 : α < 1)
    (hne : ∀ x ∈ box L, ∀ y ∈ box L, Adj x y → |h x-h y| ≤ 1-δ)
    (ht : (fillingPolytope L t).Nonempty) :
    0 < fillingVolume L (fun x => (1-α)*h x+α*t x) := by
  obtain ⟨b,hb⟩ := ht
  let a₀ : Filling L := (1-α) • (fun x : {x : Vertex // x ∈ interior L} => h x)+α • b
  apply fillingVolume_pos_of_slack (a₀:=a₀) (δ:=(1-α)*δ) (mul_pos (by linarith) hδ)
  intro x hx y hy hxy
  change |filledHeight L (fun z => (1-α)*h z+α*t z) ((1-α) • (fun z : {x : Vertex // x ∈ interior L} => h z)+α • b) x-
    filledHeight L (fun z => (1-α)*h z+α*t z) ((1-α) • (fun z : {x : Vertex // x ∈ interior L} => h z)+α • b) y| ≤ _
  rw [filledHeight_mix, filledHeight_mix, filledHeight_center, filledHeight_center]
  calc
    _ = |(1-α)*(h x-h y)+α*(filledHeight L t b x-filledHeight L t b y)| := by congr 1; ring
    _ ≤ |(1-α)*(h x-h y)|+|α*(filledHeight L t b x-filledHeight L t b y)| := abs_add_le _ _
    _ = (1-α)*|h x-h y|+α*|filledHeight L t b x-filledHeight L t b y| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1-α),abs_of_nonneg hα]
    _ ≤ (1-α)*(1-δ)+α*1 := add_le_add
      (mul_le_mul_of_nonneg_left (hne x hx y hy hxy) (by linarith))
      (mul_le_mul_of_nonneg_left (hb x hx y hy hxy) hα)
    _ = 1-(1-α)*δ := by ring

end TriangularLipschitz

end

end OAI
