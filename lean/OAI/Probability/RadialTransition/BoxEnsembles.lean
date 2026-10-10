import OAI.Probability.RadialTransition.DeletedInteractions

namespace OAI

noncomputable section


open MeasureTheory Set Filter Function

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

def halfCube (L : ℝ) : Set Position := {x | ∀ k, 0 ≤ x k ∧ x k < L}

lemma measurableSet_halfCube (L : ℝ) : MeasurableSet (halfCube L) := by
  have he : halfCube L = ⋂ k : Fin 3, {x : Position | 0 ≤ x k ∧ x k < L} := by
    ext x; simp only [halfCube, mem_ofPred_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro k
  exact (isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k)).measurableSet.inter
    (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k) continuous_const).measurableSet

lemma halfCube_ae_cube (L : ℝ) : halfCube L =ᵐ[volume] cube L := by
  have hh := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (f := fun _ => (0:ℝ)) (g := fun _ => L)
  have hp := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae hh
  filter_upwards [hp] with x hx
  apply propext
  change (∀ k, 0 ≤ x k ∧ x k < L) ↔ (∀ k, 0 ≤ x k ∧ x k ≤ L)
  have hx' := eq_iff_iff.mp hx
  simpa only [Set.pi, Set.Ico, Set.Icc, Membership.mem, Set.Mem, Set.ofPred, Set.univ, Set.mem_univ, true_implies, forall_const, Pi.le_def, forall_and] using hx'

lemma restrict_halfCube (L : ℝ) : volume.restrict (halfCube L) = volume.restrict (cube L) :=
  Measure.restrict_congr_set (halfCube_ae_cube L)

abbrev GridIndex (q : ℕ) := Fin 3 → Fin q

def gridEmbed {q : ℕ} (i : GridIndex q) : Cell := fun k => (i k : ℤ)

lemma gridEmbed_injective (q : ℕ) : Function.Injective (@gridEmbed q) := by
  intro i j h
  funext k
  apply Fin.ext
  have hh : (i k : ℤ) = (j k : ℤ) := congrFun h k
  exact_mod_cast hh

lemma halfCube_grid_cover (q : ℕ) (x : Position) (hx : x ∈ halfCube ((q:ℝ)/4)) :
    ∃ i : GridIndex q, cellOf x = gridEmbed i := by
  have hh (k : Fin 3) : 0 ≤ cellOf x k ∧ cellOf x k < (q:ℤ) := by
    constructor
    · exact Int.floor_nonneg.mpr (by nlinarith [(hx k).1])
    · apply Int.floor_lt.mpr
      exact_mod_cast (show 4*x k < (q:ℝ) by linarith [(hx k).2])
  let i : GridIndex q := fun k => ⟨(cellOf x k).toNat, by have := hh k; omega⟩
  refine ⟨i, ?_⟩
  funext k
  simp only [gridEmbed, i]
  exact (Int.toNat_of_nonneg (hh k).1).symm

lemma gridEmbed_mem_halfCube_iff {q : ℕ} (i : GridIndex q) (x : Position)
    (hx : cellOf x = gridEmbed i) : x ∈ halfCube ((q:ℝ)/4) := by
  intro k
  have hl := Int.floor_le (4*x k)
  have hu := Int.lt_floor_add_one (4*x k)
  have he : ⌊4*x k⌋ = (i k : ℤ) := congrFun hx k
  rw [he] at hl hu
  have hi : (i k : ℝ) + 1 ≤ (q:ℝ) := by exact_mod_cast (i k).isLt
  have hin : 0 ≤ (i k : ℝ) := by positivity
  constructor <;> push_cast at * <;> linarith

lemma halfCube_eq_gridUnion (q : ℕ) :
    halfCube ((q:ℝ)/4) = ⋃ i : GridIndex q, gridRegion (gridEmbed i) := by
  ext x
  simp only [mem_iUnion, gridRegion, mem_ofPred_eq]
  exact ⟨halfCube_grid_cover q x, fun ⟨i,hi⟩ => gridEmbed_mem_halfCube_iff i x hi⟩

lemma volume_halfCube (L : ℝ) : volume (halfCube L) = ENNReal.ofReal L ^ 3 := by
  rw [measure_congr (halfCube_ae_cube L), volume_cube]

def macroOf (q : ℕ) (k : Cell) : Cell := fun d => k d / (q:ℤ)

def blockEmbed {m q : ℕ} (i : GridIndex m) (j : GridIndex q) : GridIndex (m*q) :=
  fun d => ⟨(i d : ℕ)*q+(j d : ℕ), by
    calc
      _ < (i d : ℕ)*q+q := Nat.add_lt_add_left (j d).isLt _
      _ = ((i d : ℕ)+1)*q := by ring
      _ ≤ m*q := Nat.mul_le_mul_right q (Nat.succ_le_of_lt (i d).isLt)⟩

lemma blockEmbed_macro {m q : ℕ} (hq : 0 < q) (i : GridIndex m) (j : GridIndex q) :
    macroOf q (gridEmbed (blockEmbed i j)) = gridEmbed i := by
  funext d
  simp only [macroOf, gridEmbed, blockEmbed]
  have hj := (j d).isLt
  have hq' : (0:ℤ) < q := by exact_mod_cast hq
  have hj' : (0:ℤ) ≤ (j d : ℕ) ∧ (j d : ℤ) < q := by exact_mod_cast (show 0 ≤ (j d:ℕ) ∧ (j d:ℕ) < q from ⟨Nat.zero_le _, hj⟩)
  push_cast
  rw [Int.add_ediv_of_dvd_left (dvd_mul_left _ _),
    Int.mul_ediv_cancel _ (ne_of_gt hq'), Int.ediv_eq_zero_of_lt hj'.1 hj'.2, add_zero]

lemma blockEmbed_injective {m q : ℕ} (hq : 0 < q) :
    Function.Injective (fun p : GridIndex m × GridIndex q => blockEmbed p.1 p.2) := by
  intro p r h
  have hi : p.1 = r.1 := gridEmbed_injective m (by
    have := congrArg (fun k => macroOf q (gridEmbed k)) h
    simpa only [blockEmbed_macro hq] using this)
  apply Prod.ext hi
  funext d
  apply Fin.ext
  have hh := congrArg (fun k : GridIndex (m*q) => (k d : ℕ)) h
  simp only [blockEmbed, hi] at hh
  omega

lemma blockEmbed_surjective {m q : ℕ} (hq : 0 < q) :
    Function.Surjective (fun p : GridIndex m × GridIndex q => blockEmbed p.1 p.2) := by
  intro k
  let i : GridIndex m := fun d => ⟨(k d : ℕ)/q, Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm m q] using (k d).isLt)⟩
  let j : GridIndex q := fun d => ⟨(k d : ℕ)%q, Nat.mod_lt _ hq⟩
  refine ⟨(i,j), ?_⟩
  funext d
  apply Fin.ext
  simpa only [blockEmbed, i, j, Nat.mul_comm] using Nat.div_add_mod (k d : ℕ) q

def boundaryCoord (q D : ℕ) : Finset (Fin q) :=
  Finset.univ.filter (fun a => (a:ℕ) < D ∨ q-D ≤ (a:ℕ))

lemma card_boundaryCoord (q D : ℕ) : (boundaryCoord q D).card ≤ 2*D := by
  let lo := Finset.univ.filter (fun a : Fin q => (a:ℕ) < D)
  let hi := Finset.univ.filter (fun a : Fin q => q-D ≤ (a:ℕ))
  have hlo : lo.card ≤ D := by
    calc
      _ ≤ (Finset.range D).card := Finset.card_le_card_of_injOn Fin.val
        (by intro a ha; exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2)
        (fun a _ b _ h => Fin.ext h)
      _ = D := Finset.card_range D
  have hhi : hi.card ≤ D := by
    calc
      _ ≤ (Finset.range D).card := Finset.card_le_card_of_injOn (fun a : Fin q => q-1-(a:ℕ))
        (by intro a ha; have hh := (Finset.mem_filter.mp ha).2; have := a.isLt; apply Finset.mem_range.mpr; change q-1-(a:ℕ) < D; omega)
        (by intro a ha b hb h; apply Fin.ext; have := a.isLt; have := b.isLt; change q-1-(a:ℕ) = q-1-(b:ℕ) at h; omega)
      _ = D := Finset.card_range D
  have he : boundaryCoord q D = lo ∪ hi := by
    ext a; simp only [boundaryCoord, lo, hi, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [he]
  exact le_trans (Finset.card_union_le lo hi) (by omega)

def boundarySlice (q D : ℕ) (d : Fin 3) : Finset (GridIndex q) :=
  Fintype.piFinset (fun k => if k = d then boundaryCoord q D else Finset.univ)

def boundaryGrid (q D : ℕ) : Finset (GridIndex q) :=
  Finset.univ.biUnion (boundarySlice q D)

lemma mem_boundaryGrid {q D : ℕ} {j : GridIndex q} :
    j ∈ boundaryGrid q D ↔ ∃ d, (j d:ℕ) < D ∨ q-D ≤ (j d:ℕ) := by
  simp only [boundaryGrid, Finset.mem_biUnion, Finset.mem_univ, true_and,
    boundarySlice, Fintype.mem_piFinset]
  constructor
  · rintro ⟨d,hd⟩
    refine ⟨d, ?_⟩
    have h := hd d
    simpa only [ite_true, boundaryCoord, Finset.mem_filter, Finset.mem_univ, true_and] using h
  · rintro ⟨d,hd⟩
    refine ⟨d, ?_⟩
    intro k
    split_ifs with h
    · subst k
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
    · exact Finset.mem_univ _

lemma card_boundaryGrid (q D : ℕ) : (boundaryGrid q D).card ≤ 6*D*q^2 := by
  have hs (d : Fin 3) : (boundarySlice q D d).card = (boundaryCoord q D).card*q^2 := by
    rw [boundarySlice, Fintype.card_piFinset]
    fin_cases d <;> simp [Fin.prod_univ_three] <;> ring
  calc
    _ ≤ ∑ d : Fin 3, (boundarySlice q D d).card := Finset.card_biUnion_le
    _ = 3*((boundaryCoord q D).card*q^2) := by simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ 3*(2*D*q^2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (card_boundaryCoord q D))
    _ = _ := by ring

lemma inner_block_macro {m q D : ℕ} (hq : 0 < q) (i : GridIndex m) (j : GridIndex q)
    (hj : j ∉ boundaryGrid q D) {k : Cell}
    (hk : ∀ d, |k d-gridEmbed (blockEmbed i j) d| ≤ (D:ℤ)) :
    macroOf q k = gridEmbed i := by
  have hj' : ∀ d, D ≤ (j d:ℕ) ∧ (j d:ℕ)+D < q := by
    have hh := mt mem_boundaryGrid.mpr hj
    intro d
    have hn : ¬ ((j d:ℕ) < D ∨ q-D ≤ (j d:ℕ)) := fun h => hh ⟨d,h⟩
    omega
  funext d
  apply (Int.ediv_eq_iff_of_pos (by exact_mod_cast hq)).mpr
  have hkd := abs_le.mp (hk d)
  have hlow : (D:ℤ) ≤ (j d:ℤ) := by exact_mod_cast (hj' d).1
  have hupp : (j d:ℤ)+(D:ℤ) < (q:ℤ) := by exact_mod_cast (hj' d).2
  change -(D:ℤ) ≤ k d-((i d:ℕ)*q+(j d:ℕ):ℕ) ∧ k d-((i d:ℕ)*q+(j d:ℕ):ℕ) ≤ (D:ℤ) at hkd
  push_cast at hkd
  change (i d:ℤ)*(q:ℤ) ≤ k d ∧ k d < (i d:ℤ)*(q:ℤ)+(q:ℤ)
  constructor <;> omega

lemma sum_blockGrid {m q : ℕ} (hq : 0 < q) (F : GridIndex (m*q) → ℝ) :
    ∑ k, F k = ∑ i : GridIndex m, ∑ j : GridIndex q, F (blockEmbed i j) := by
  have hh := Fintype.sum_equiv (Equiv.ofBijective _ ⟨blockEmbed_injective (m := m) hq, blockEmbed_surjective hq⟩)
    (fun p => F (blockEmbed p.1 p.2)) F (fun _ => rfl)
  rw [Fintype.sum_prod_type] at hh
  exact hh.symm

lemma grid_sum_boundary_bound {m q D : ℕ} (hq : 0 < q) {C : ℝ} (hC : 0 ≤ C)
    (F : GridIndex (m*q) → ℝ)
    (hF : ∀ k, F k ≤ C)
    (hzero : ∀ i j, j ∉ boundaryGrid q D → F (blockEmbed i j) = 0) :
    ∑ k, F k ≤ (m:ℝ)^3*(6*D*q^2)*C := by
  rw [sum_blockGrid hq]
  have hsum (i : GridIndex m) : ∑ j : GridIndex q, F (blockEmbed i j) ≤ (6*D*q^2:ℕ)*C := by
    calc
      _ = ∑ j ∈ boundaryGrid q D, F (blockEmbed i j) :=
        (Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hzero i j hj)).symm
      _ ≤ ∑ _j ∈ boundaryGrid q D, C := Finset.sum_le_sum (fun j _ => hF _)
      _ = ((boundaryGrid q D).card:ℝ)*C := by simp
      _ ≤ (6*D*q^2:ℕ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast card_boundaryGrid q D) hC
  calc
    _ ≤ ∑ _i : GridIndex m, (6*D*q^2:ℕ)*C := Finset.sum_le_sum (fun i _ => hsum i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; push_cast; ring

end RadialTransition

end

end OAI
