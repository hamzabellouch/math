import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.RectangleContours

namespace OAI

/-! Exact clipped-square lattice tilings and geometric weights. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open Set Filter Complex Complex.HadamardThreeLines
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.RectangleTiling

theorem interval_index (r M : ℕ) (hr : 0<r) (d : ℤ) (hd : 0≤d) (hupper : d<(M:ℤ)*r) :
    ∃ i : Fin M, (i.val:ℤ)*r ≤ d ∧ d<((i.val:ℤ)+1)*r := by
  have hr' : 0<(r:ℤ) := by exact_mod_cast hr
  let k := d/(r:ℤ)
  have hk0 : 0≤k := Int.ediv_nonneg hd (le_of_lt hr')
  have hkM : k<(M:ℤ) := Int.ediv_lt_of_lt_mul hr' hupper
  let i : Fin M := ⟨k.toNat,by omega⟩
  have hi : (i.val:ℤ)=k := Int.toNat_of_nonneg hk0
  refine ⟨i,?_,?_⟩ <;> rw [hi]
  · have h := Int.ediv_mul_add_emod d r
    have hm := Int.emod_nonneg d (ne_of_gt hr')
    change d/(r:ℤ)*(r:ℤ) ≤ d
    omega
  · have h := Int.ediv_mul_add_emod d r
    have hm := Int.emod_lt_of_pos d hr'
    change d<(d/(r:ℤ)+1)*(r:ℤ)
    nlinarith only [h,hm]

theorem interval_unique (r : ℕ) (hr : 0<r) (i j : ℕ) (d : ℤ)
    (hi : (i:ℤ)*r≤d ∧ d<((i:ℤ)+1)*r)
    (hj : (j:ℤ)*r≤d ∧ d<((j:ℤ)+1)*r) : i=j := by
  have hr' : 0<(r:ℤ) := by exact_mod_cast hr
  by_contra hn
  rcases lt_or_gt_of_ne hn with hl | hl
  · have hc : (i:ℤ)+1≤ j := by exact_mod_cast hl
    have hm := mul_le_mul_of_nonneg_right hc (le_of_lt hr')
    linarith only [hi.2,hj.1,hm]
  · have hc : (j:ℤ)+1≤ i := by exact_mod_cast hl
    have hm := mul_le_mul_of_nonneg_right hc (le_of_lt hr')
    linarith only [hj.2,hi.1,hm]

theorem index_near (r b : ℕ) (hr : 0<r) (i j : ℕ) (d : ℤ)
    (hi : (i:ℤ)*r-(b:ℤ)*r≤d ∧ d<((i:ℤ)+1)*r+(b:ℤ)*r)
    (hj : (j:ℤ)*r≤d ∧ d<((j:ℤ)+1)*r) : i≤ j+b ∧ j≤ i+b := by
  have hr' : 0<(r:ℤ) := by exact_mod_cast hr
  constructor
  · by_contra hn
    have hn' : (j:ℤ)+b+1≤ i := by exact_mod_cast (Nat.lt_of_not_ge hn)
    have hm := mul_le_mul_of_nonneg_right hn' (le_of_lt hr')
    nlinarith only [hi.1,hj.2,hm]
  · by_contra hn
    have hn' : (i:ℤ)+b+1≤ j := by exact_mod_cast (Nat.lt_of_not_ge hn)
    have hm := mul_le_mul_of_nonneg_right hn' (le_of_lt hr')
    nlinarith only [hi.2,hj.1,hm]

theorem mod_near_unique (b i j : ℕ) (hp : i%(b+1)=j%(b+1))
    (hi : i≤ j+b) (hj : j≤ i+b) : i=j := by
  have hm : Int.ModEq ((b:ℤ)+1) (i:ℤ) (j:ℤ) := by
    change (i:ℤ)%((b:ℤ)+1)=(j:ℤ)%((b:ℤ)+1)
    exact_mod_cast hp
  by_cases hij : i≤ j
  · have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (show 0≤(j:ℤ)-i by omega) (show (j:ℤ)-i<(b:ℤ)+1 by omega) hm.dvd
    omega
  · have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (show 0≤(i:ℤ)-j by omega) (show (i:ℤ)-j<(b:ℤ)+1 by omega) hm.symm.dvd
    omega

end PolynomialPEPS.Subvolume.RectangleTiling

namespace PolynomialPEPS.Subvolume.RectangleTiling
open scoped BigOperators
open RectangleContours
variable {L M : ℕ}

abbrev Index (M : ℕ) := Fin M × Fin M

def tile (lo₁ lo₂ : ℤ) (r : ℕ) (i : Index M) : Finset (Vertex L) :=
  rectangle (lo₁+(i.1.val:ℤ)*r) (lo₁+((i.1.val:ℤ)+1)*r-1)
    (lo₂+(i.2.val:ℤ)*r) (lo₂+((i.2.val:ℤ)+1)*r-1) 0

def collar (lo₁ lo₂ : ℤ) (r b : ℕ) (i : Index M) : Finset (Vertex L) :=
  rectangle (lo₁+(i.1.val:ℤ)*r) (lo₁+((i.1.val:ℤ)+1)*r-1)
    (lo₂+(i.2.val:ℤ)*r) (lo₂+((i.2.val:ℤ)+1)*r-1) (b*r)

def box (lo₁ lo₂ : ℤ) (M r : ℕ) : Finset (Vertex L) :=
  rectangle lo₁ (lo₁+(M:ℤ)*r-1) lo₂ (lo₂+(M:ℤ)*r-1) 0

lemma mem_tile (lo₁ lo₂ : ℤ) (r : ℕ) (i : Index M) (v : Vertex L) :
    v∈tile lo₁ lo₂ r i ↔
      ((i.1.val:ℤ)*r≤(v.1.val:ℤ)-lo₁ ∧ (v.1.val:ℤ)-lo₁<((i.1.val:ℤ)+1)*r) ∧
      ((i.2.val:ℤ)*r≤(v.2.val:ℤ)-lo₂ ∧ (v.2.val:ℤ)-lo₂<((i.2.val:ℤ)+1)*r) := by
  simp only [tile,mem_rectangle,Nat.cast_zero,sub_zero,add_zero]
  omega

lemma mem_collar (lo₁ lo₂ : ℤ) (r b : ℕ) (i : Index M) (v : Vertex L) :
    v∈collar lo₁ lo₂ r b i ↔
      ((i.1.val:ℤ)*r-(b:ℤ)*r≤(v.1.val:ℤ)-lo₁ ∧
        (v.1.val:ℤ)-lo₁<((i.1.val:ℤ)+1)*r+(b:ℤ)*r) ∧
      ((i.2.val:ℤ)*r-(b:ℤ)*r≤(v.2.val:ℤ)-lo₂ ∧
        (v.2.val:ℤ)-lo₂<((i.2.val:ℤ)+1)*r+(b:ℤ)*r) := by
  simp only [collar,mem_rectangle,Nat.cast_mul]
  omega

lemma mem_box (lo₁ lo₂ : ℤ) (M r : ℕ) (v : Vertex L) :
    v∈box lo₁ lo₂ M r ↔
      (0≤(v.1.val:ℤ)-lo₁ ∧ (v.1.val:ℤ)-lo₁<(M:ℤ)*r) ∧
      (0≤(v.2.val:ℤ)-lo₂ ∧ (v.2.val:ℤ)-lo₂<(M:ℤ)*r) := by
  simp only [box,mem_rectangle,Nat.cast_zero,sub_zero,add_zero]
  omega

lemma tile_subset_box (lo₁ lo₂ : ℤ) (r : ℕ) (i : Index M) :
    tile (L:=L) lo₁ lo₂ r i ⊆ box lo₁ lo₂ M r := by
  intro v hv
  rw [mem_tile] at hv
  rw [mem_box]
  have h1 : (i.1.val:ℤ)+1≤M := by exact_mod_cast i.1.isLt
  have h2 : (i.2.val:ℤ)+1≤M := by exact_mod_cast i.2.isLt
  have hr : 0≤(r:ℤ) := Nat.cast_nonneg _
  have hm1 := mul_le_mul_of_nonneg_right h1 hr
  have hm2 := mul_le_mul_of_nonneg_right h2 hr
  have hn1 : 0≤(i.1.val:ℤ)*(r:ℤ) := mul_nonneg (Nat.cast_nonneg _) hr
  have hn2 : 0≤(i.2.val:ℤ)*(r:ℤ) := mul_nonneg (Nat.cast_nonneg _) hr
  constructor <;> constructor <;> omega

lemma tiles_cover (lo₁ lo₂ : ℤ) (r : ℕ) (hr : 0<r) :
    Finset.univ.biUnion (tile (L:=L) (M:=M) lo₁ lo₂ r)=box lo₁ lo₂ M r := by
  classical
  apply Finset.Subset.antisymm
  · exact Finset.biUnion_subset.mpr (fun i _ => tile_subset_box lo₁ lo₂ r i)
  · intro v hv
    rw [mem_box] at hv
    obtain ⟨i,hi⟩ := interval_index r M hr ((v.1.val:ℤ)-lo₁) hv.1.1 hv.1.2
    obtain ⟨j,hj⟩ := interval_index r M hr ((v.2.val:ℤ)-lo₂) hv.2.1 hv.2.2
    exact Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_univ _,(mem_tile lo₁ lo₂ r (i,j) v).mpr ⟨hi,hj⟩⟩

lemma tiles_disjoint (lo₁ lo₂ : ℤ) (r : ℕ) (hr : 0<r) (i j : Index M) (hij : i≠j) :
    Disjoint (tile (L:=L) lo₁ lo₂ r i) (tile lo₁ lo₂ r j) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  rw [mem_tile] at hv hw
  have h1 := interval_unique r hr i.1 j.1 ((v.1.val:ℤ)-lo₁) hv.1 hw.1
  have h2 := interval_unique r hr i.2 j.2 ((v.2.val:ℤ)-lo₂) hv.2 hw.2
  exact hij (Prod.ext (Fin.ext h1) (Fin.ext h2))

def color (b : ℕ) (i : Index M) : Index (b+1) :=
  (⟨i.1.val%(b+1),Nat.mod_lt _ (by omega)⟩,⟨i.2.val%(b+1),Nat.mod_lt _ (by omega)⟩)

def interior (b M : ℕ) : Finset (Index M) :=
  Finset.univ.filter (fun i => b≤ i.1.val ∧ i.1.val+b<M ∧ b≤ i.2.val ∧ i.2.val+b<M)

lemma collar_subset_box (lo₁ lo₂ : ℤ) (r b : ℕ) (i : Index M) (hi : i∈interior b M) :
    collar (L:=L) lo₁ lo₂ r b i ⊆ box lo₁ lo₂ M r := by
  have hi := (Finset.mem_filter.mp hi).2
  intro v hv
  rw [mem_collar] at hv
  rw [mem_box]
  have hr : 0≤(r:ℤ) := Nat.cast_nonneg _
  have h1 : (b:ℤ)≤ i.1.val := by exact_mod_cast hi.1
  have h2 : (i.1.val:ℤ)+1+b≤M := by
    have hh : (i.1.val:ℤ)+b<M := by exact_mod_cast hi.2.1
    omega
  have h3 : (b:ℤ)≤ i.2.val := by exact_mod_cast hi.2.2.1
  have h4 : (i.2.val:ℤ)+1+b≤M := by
    have hh : (i.2.val:ℤ)+b<M := by exact_mod_cast hi.2.2.2
    omega
  have hm1 := mul_le_mul_of_nonneg_right h1 hr
  have hm2 := mul_le_mul_of_nonneg_right h2 hr
  have hm3 := mul_le_mul_of_nonneg_right h3 hr
  have hm4 := mul_le_mul_of_nonneg_right h4 hr
  constructor <;> constructor <;> nlinarith only [hv,hm1,hm2,hm3,hm4]

lemma same_color_disjoint_collar (lo₁ lo₂ : ℤ) (r b : ℕ) (hr : 0<r)
    (i j : Index M) (hc : color b i=color b j) (hij : i≠j) :
    Disjoint (collar (L:=L) lo₁ lo₂ r b i) (tile lo₁ lo₂ r j) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  rw [mem_collar] at hv
  rw [mem_tile] at hw
  have h1 := index_near r b hr i.1 j.1 ((v.1.val:ℤ)-lo₁) hv.1 hw.1
  have h2 := index_near r b hr i.2 j.2 ((v.2.val:ℤ)-lo₂) hv.2 hw.2
  have e1 : i.1.val%(b+1)=j.1.val%(b+1) := congrArg (fun x : Index (b+1) => x.1.val) hc
  have e2 : i.2.val%(b+1)=j.2.val%(b+1) := congrArg (fun x : Index (b+1) => x.2.val) hc
  exact hij (Prod.ext (Fin.ext (mod_near_unique b _ _ e1 h1.1 h1.2))
    (Fin.ext (mod_near_unique b _ _ e2 h2.1 h2.2)))

lemma collar_exposed (lo₁ lo₂ : ℤ) (r b : ℕ) (hr : 0<r)
    (i : Index M) (hi : i∈interior b M) :
    collar (L:=L) lo₁ lo₂ r b i\tile lo₁ lo₂ r i ⊆
      (Finset.univ\(interior b M).filter (fun j => color b j=color b i)).biUnion (tile lo₁ lo₂ r) := by
  classical
  intro v hv
  have hvB := collar_subset_box lo₁ lo₂ r b i hi (Finset.mem_sdiff.mp hv).1
  rw [← tiles_cover lo₁ lo₂ r hr] at hvB
  obtain ⟨j,hj,hvJ⟩ := Finset.mem_biUnion.mp hvB
  apply Finset.mem_biUnion.mpr
  refine ⟨j,Finset.mem_sdiff.mpr ⟨hj,?_⟩,hvJ⟩
  intro hbad
  have hc := (Finset.mem_filter.mp hbad).2
  have hne : i≠j := by
    intro h; subst j; exact (Finset.mem_sdiff.mp hv).2 hvJ
  exact Finset.disjoint_left.mp (same_color_disjoint_collar lo₁ lo₂ r b hr i j hc.symm hne)
    (Finset.mem_sdiff.mp hv).1 hvJ

end PolynomialPEPS.Subvolume.RectangleTiling

namespace PolynomialPEPS.Subvolume.RectangleTiling
open scoped BigOperators

theorem interior_card_lower (b : ℕ) :
    (2*(b+1))^2 ≤ (interior b (4*(b+1))).card := by
  let f : Index (2*(b+1)) → {i : Index (4*(b+1)) // i∈interior b (4*(b+1))} :=
    fun i => ⟨(⟨i.1.val+b,by have := i.1.isLt; omega⟩,
      ⟨i.2.val+b,by have := i.2.isLt; omega⟩),by
        simp only [interior,Finset.mem_filter,Finset.mem_univ,true_and]
        have h1 := i.1.isLt
        have h2 := i.2.isLt
        omega⟩
  have hf : Function.Injective f := by
    intro i j h
    have e1 := congrArg (fun z => z.val.1.val) h
    have e2 := congrArg (fun z => z.val.2.val) h
    apply Prod.ext <;> apply Fin.ext
    · change i.1.val+b=j.1.val+b at e1
      omega
    · change i.2.val+b=j.2.val+b at e2
      omega
  have ht := Fintype.card_le_of_injective f hf
  simpa only [Index,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,pow_two] using ht

theorem interior_card_upper (b M : ℕ) : (interior b M).card ≤ M^2 := by
  have h := Finset.card_le_card (show interior b M ⊆ Finset.univ from Finset.subset_univ _)
  simpa only [Finset.card_univ,Index,Fintype.card_prod,Fintype.card_fin,pow_two] using h

end PolynomialPEPS.Subvolume.RectangleTiling

end

end OAI
