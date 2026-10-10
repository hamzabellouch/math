import OAI.Geometry.LatticeCovering.CircuitErrors

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.PrimeKernel
open LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scaleFactor (p : ℕ) : ℝ := (p : ℝ)^(-(Fintype.card ι : ℝ)⁻¹)
lemma scaleFactor_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) : 0 < scaleFactor (ι := ι) p :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp) _

def normalizeEquiv (p : ℕ) (hp : 0 < p) : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (scaleFactor (ι := ι) p) (scaleFactor_pos p hp).ne'

lemma normalizeEquiv_det (p : ℕ) (hp : 0 < p) (i : ι) :
    LinearMap.det (normalizeEquiv (ι := ι) p hp).toLinearMap=(p : ℝ)⁻¹ := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩).ne'
  change LinearMap.det (scaleFactor (ι := ι) p • (LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))=_
  rw [LinearMap.det_smul,LinearMap.det_id,mul_one,Module.finrank_pi]
  rw [scaleFactor,←Real.rpow_natCast,←Real.rpow_mul hpR.le]
  have he : -(Fintype.card ι : ℝ)⁻¹*(Fintype.card ι : ℝ) = -1 := by field_simp
  rw [he,Real.rpow_neg_one]

abbrev normalized (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) : Submodule ℤ (ι → ℝ) :=
  image (lattice p hp i a) (normalizeEquiv p hp)

lemma covolume_normalized (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    ZLattice.covolume (normalized p hp i a)=1 := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  rw [image_covolume,normalizeEquiv_det p hp i,covolume_lattice,
    abs_of_pos (inv_pos.mpr hpR),inv_mul_cancel₀ hpR.ne']


def gridMap (p : ℕ) (hp : 0 < p) : (ι → ℤ) →+ (ι → ℝ) where
  toFun z := normalizeEquiv p hp (fun j => (z j : ℝ))
  map_zero' := by
    simp only [Pi.zero_apply,Int.cast_zero]
    exact map_zero (normalizeEquiv (ι := ι) p hp)
  map_add' z w := by
    change normalizeEquiv p hp (fun j => ((z+w) j : ℝ))=_
    rw [show (fun j => ((z+w) j : ℝ)) = (fun j => (z j : ℝ))+(fun j => (w j : ℝ)) by
      ext j; simp]
    exact map_add _ _ _

lemma gridMap_injective (p : ℕ) (hp : 0 < p) : Function.Injective (gridMap (ι := ι) p hp) := by
  intro z w h
  have he := (normalizeEquiv p hp).injective h
  ext j
  exact_mod_cast congrFun he j

def modForm (p : ℕ) (i : ι) (a : ι → ℤ) : (ι → ℤ) →+ ZMod p where
  toFun z := (z i : ZMod p)+∑ j ∈ Finset.univ.erase i, (a j : ZMod p)*(z j : ZMod p)
  map_zero' := by simp
  map_add' z w := by
    simp only [Pi.add_apply,Int.cast_add,mul_add,Finset.sum_add_distrib]
    ring

lemma grid_mem_normalized_iff (p : ℕ) (hp : 0 < p) (i : ι) (a z : ι → ℤ) :
    gridMap p hp z ∈ normalized p hp i a ↔ modForm p i a z=0 := by
  change (normalizeEquiv p hp) (fun j => (z j : ℝ)) ∈
    image (lattice p hp i a) (normalizeEquiv p hp) ↔ _
  change (normalizeEquiv p hp).symm ((normalizeEquiv p hp) (fun j => (z j : ℝ))) ∈ lattice p hp i a ↔ _
  rw [LinearEquiv.symm_apply_apply,integer_mem_iff_congruence]
  rfl

lemma exists_grid_of_mem (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ)
    {x : ι → ℝ} (hx : x ∈ normalized p hp i a) :
    ∃ z : ι → ℤ, gridMap p hp z=x ∧ modForm p i a z=0 := by
  obtain ⟨l,hl,he⟩ := (LatticeGeometry.mem_image _ _ _).mp hx
  obtain ⟨z,hz⟩ := exists_integer_of_mem p hp i a hl
  have hg : gridMap p hp z=x := by change normalizeEquiv p hp (fun j => (z j : ℝ))=x; rw [hz,he]
  exact ⟨z,hg,(grid_mem_normalized_iff p hp i a z).mp (hg.symm ▸ hx)⟩



def kernelEquiv (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    (modForm p i a).ker ≃+ normalized p hp i a :=
  AddEquiv.ofBijective
    ({ toFun := fun z => ⟨gridMap p hp z,(grid_mem_normalized_iff p hp i a z).mpr z.property⟩
       map_zero' := by apply Subtype.ext; exact map_zero _
       map_add' := fun z w => by apply Subtype.ext; exact map_add _ _ _ } :
      (modForm p i a).ker →+ normalized p hp i a)
    ⟨by intro z w h; apply Subtype.ext; exact gridMap_injective p hp (congrArg Subtype.val h),by
      intro x
      obtain ⟨z,hz,h0⟩ := exists_grid_of_mem p hp i a x.property
      exact ⟨⟨z,h0⟩,Subtype.ext hz⟩⟩



end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



def rectangularCell (p : ℕ) (i : ι) : Set (ι → ℝ) :=
  Set.univ.pi (fun j => Set.Ico (0:ℝ) (if j=i then (p:ℝ) else 1))

lemma mem_rectangularCell_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (i : ι) (x : ι → ℝ) :
    x ∈ rectangularCell p i ↔ ∀ j, 0 ≤ x j ∧ x j < (if j=i then (p:ℝ) else 1) := by
  simp [rectangularCell,Set.mem_pi]

lemma rectangularCell_measurable (p : ℕ) (i : ι) : MeasurableSet (rectangularCell p i) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

lemma integer_displacement_unique {p : ℕ} (hp : 0 < p) (i : ι)
    (a : ι → ℤ) {x y : ι → ℝ} (hx : x ∈ rectangularCell p i)
    (hy : y ∈ rectangularCell p i) (hxy : x-y ∈ lattice p hp i a) : x=y := by
  obtain ⟨z,hz,hdiv⟩ := (mem_lattice_iff p hp i a (x-y)).mp hxy
  have hzj : ∀ j, (z j:ℝ)=x j-y j := fun j => congrFun hz j
  have hxx := (mem_rectangularCell_iff p i x).mp hx
  have hyy := (mem_rectangularCell_iff p i y).mp hy
  have htail (j : ι) (hj : j ≠ i) : z j=0 := by
    have hxj := hxx j
    have hyj := hyy j
    rw [ite_eq_right hj] at hxj hyj
    have hlow : (-1:ℝ) < z j := by linarith [hzj j]
    have hupp : (z j:ℝ) < 1 := by linarith [hzj j]
    have hlowZ : (-1:ℤ) < z j := by exact_mod_cast hlow
    have huppZ : z j < 1 := by exact_mod_cast hupp
    omega
  have hsum : ∑ j ∈ Finset.univ.erase i, a j*z j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [htail j (Finset.mem_erase.mp hj).1,mul_zero]
  rw [hsum,add_zero] at hdiv
  obtain ⟨q,hq⟩ := hdiv
  have hxi := hxx i
  have hyi := hyy i
  simp at hxi hyi
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hzq : (z i:ℝ)=(p:ℝ)*(q:ℝ) := by exact_mod_cast hq
  have hqlo : (-1:ℝ) < q := by nlinarith [hzj i]
  have hqhi : (q:ℝ) < 1 := by nlinarith [hzj i]
  have hqloZ : (-1:ℤ) < q := by exact_mod_cast hqlo
  have hqhiZ : q < 1 := by exact_mod_cast hqhi
  have hq0 : q=0 := by omega
  have hzi : z i=0 := by rw [hq,hq0,mul_zero]
  ext j
  by_cases hj : j=i
  · subst j
    have hh := hzj i
    rw [hzi,Int.cast_zero] at hh
    linarith
  · have hh := hzj j
    rw [htail j hj,Int.cast_zero] at hh
    linarith

lemma rectangularCell_exists_shift (p : ℕ) (hp : 0 < p) (i : ι)
    (a : ι → ℤ) (x : ι → ℝ) :
    ∃ g : lattice p hp i a, (g:ι → ℝ)+x ∈ rectangularCell p i := by
  let f : ι → ℤ := fun j => ⌊x j⌋
  let T : ℤ := f i+∑ j ∈ Finset.univ.erase i, a j*f j
  let b : ℤ := T % (p:ℤ)
  let z : ι → ℤ := Function.update (-f) i (-f i+b)
  have hb0 : 0 ≤ b := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  have hbp : b < (p:ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
  have hzj (j : ι) (hj : j ≠ i) : z j = -f j := by simp [z,Function.update_of_ne hj]
  have hzi : z i = -f i+b := by simp [z]
  have hzlat : (fun j => (z j:ℝ)) ∈ lattice p hp i a := by
    apply (integer_mem_iff_dvd p hp i a z).mpr
    have hs : ∑ j ∈ Finset.univ.erase i, a j*z j = -(∑ j ∈ Finset.univ.erase i, a j*f j) := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hzj j (Finset.mem_erase.mp hj).1,mul_neg]
    rw [hzi,hs]
    have he : -f i+b-(∑ j ∈ Finset.univ.erase i, a j*f j) = -(T-b) := by dsimp [T]; ring
    change (p:ℤ) ∣ -f i+b-(∑ j ∈ Finset.univ.erase i, a j*f j)
    rw [he]
    apply dvd_neg.mpr
    exact Int.dvd_self_sub_emod
  refine ⟨⟨fun j => (z j:ℝ),hzlat⟩,?_⟩
  rw [mem_rectangularCell_iff]
  intro j
  have hflo := Int.floor_le (x j)
  have hfhi := Int.lt_floor_add_one (x j)
  change 0 ≤ (z j:ℝ)+x j ∧ (z j:ℝ)+x j < _
  change (f j:ℝ) ≤ x j at hflo
  change x j < (f j:ℝ)+1 at hfhi
  by_cases hj : j=i
  · subst j
    rw [hzi,Int.cast_add,Int.cast_neg,ite_eq_left rfl]
    have hbR : (0:ℝ)≤b := by exact_mod_cast hb0
    have hbpR : (b:ℝ)+1≤p := by exact_mod_cast (show b+1≤(p:ℤ) by omega)
    constructor <;> linarith
  · rw [hzj j hj,Int.cast_neg,ite_eq_right hj]
    constructor <;> linarith

lemma rectangularCell_fundamental (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    IsAddFundamentalDomain (lattice p hp i a) (rectangularCell p i) volume := by
  apply IsAddFundamentalDomain.mk' (rectangularCell_measurable p i).nullMeasurableSet
  intro x
  obtain ⟨g,hg⟩ := rectangularCell_exists_shift p hp i a x
  refine ⟨g,hg,?_⟩
  intro h hh
  apply Subtype.ext
  have he := integer_displacement_unique hp i a hh hg (by
    change ((h:ι → ℝ)+x)-((g:ι → ℝ)+x) ∈ lattice p hp i a
    simpa only [add_sub_add_right_eq_sub] using (lattice p hp i a).sub_mem h.property g.property)
  exact add_right_cancel he


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev normalizedRectangularCell (p : ℕ) (hp : 0 < p) (i : ι) : Set (ι → ℝ) :=
  normalizeEquiv p hp '' rectangularCell p i

lemma normalizedRectangularCell_fundamental (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    IsAddFundamentalDomain (normalized p hp i a) (normalizedRectangularCell p hp i) volume := by
  let e := normalizeEquiv (ι:=ι) p hp
  let eg : normalized p hp i a ≃ lattice p hp i a :=
    { toFun := fun x => ⟨e.symm x,x.property⟩
      invFun := fun x => ⟨e x,by change e.symm (e x) ∈ lattice p hp i a; simp⟩
      left_inv := fun x => by apply Subtype.ext; exact e.apply_symm_apply x
      right_inv := fun x => by apply Subtype.ext; exact e.symm_apply_apply x }
  have he : LinearMap.det e.symm.toLinearMap ≠ 0 := (LinearEquiv.isUnit_det' e.symm).ne_zero
  have hf := Measure.LinearMap.quasiMeasurePreserving volume e.symm.toLinearMap he
  apply (rectangularCell_fundamental p hp i a).image_of_equiv e.toEquiv hf eg
  intro g x
  change e ((e.symm (g:ι → ℝ))+x)=(g:ι → ℝ)+e x
  rw [map_add,e.apply_symm_apply]

lemma rectangularCell_bounded (p : ℕ) (i : ι) : Bornology.IsBounded (rectangularCell p i) := by
  apply Bornology.IsBounded.subset (isCompact_Icc : IsCompact (Set.Icc (0:ι → ℝ) (fun j => if j=i then (p:ℝ) else 1))).isBounded
  intro x hx
  rw [mem_rectangularCell_iff] at hx
  exact ⟨fun j => (hx j).1,fun j => (hx j).2.le⟩

lemma normalizedRectangularCell_measurable (p : ℕ) (hp : 0 < p) (i : ι) :
    MeasurableSet (normalizedRectangularCell p hp i) :=
  (normalizeEquiv p hp).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
    (rectangularCell_measurable p i)

lemma volume_rectangularCell (p : ℕ) (i : ι) : volume (rectangularCell p i)=(p:ℝ≥0∞) := by
  classical
  rw [rectangularCell,volume_pi,Measure.pi_pi]
  simp only [Real.volume_Ico,sub_zero]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

lemma volume_normalizedRectangularCell (p : ℕ) (hp : 0 < p) (i : ι) :
    volume (normalizedRectangularCell p hp i)=1 := by
  change volume ((normalizeEquiv (ι:=ι) p hp).toContinuousLinearEquiv '' rectangularCell p i)=1
  rw [Measure.addHaar_image_continuousLinearEquiv]
  change ENNReal.ofReal |LinearMap.det (normalizeEquiv (ι:=ι) p hp).toLinearMap| * volume (rectangularCell p i)=1
  rw [normalizeEquiv_det p hp i,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)),volume_rectangularCell]
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hp),ENNReal.ofReal_natCast]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hp.ne') (by simp)



end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gridUnitCell : Set (ι → ℝ) := Set.univ.pi (fun _ => Set.Ico (0:ℝ) 1)
def offsetVector (i : ι) (b : ℤ) : ι → ℤ := Pi.single i b

def offsetCell (p : ℕ) (hp : 0 < p) (i : ι) (b : Fin p) : Set (ι → ℝ) :=
  normalizeEquiv p hp '' ((fun j => ((offsetVector i b.val j:ℤ):ℝ)) +ᵥ gridUnitCell)

lemma volume_gridUnitCell {ι : Type*} [Fintype ι] [DecidableEq ι] : volume (gridUnitCell (ι:=ι))=1 := by
  rw [gridUnitCell,volume_pi,Measure.pi_pi]
  simp

lemma volume_offsetCell (p : ℕ) (hp : 0 < p) (i : ι) (b : Fin p) :
    volume (offsetCell p hp i b)=(p:ℝ≥0∞)⁻¹ := by
  change volume ((normalizeEquiv (ι:=ι) p hp).toContinuousLinearEquiv '' _)=_
  rw [Measure.addHaar_image_continuousLinearEquiv]
  change ENNReal.ofReal |LinearMap.det (normalizeEquiv (ι:=ι) p hp).toLinearMap| * volume _ = _
  rw [normalizeEquiv_det p hp i,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)),
    measure_vadd,volume_gridUnitCell,mul_one,ENNReal.ofReal_inv_of_pos (by exact_mod_cast hp),
    ENNReal.ofReal_natCast]

lemma rectangularCell_unit_decomposition (p : ℕ) (hp : 0 < p) (i : ι)
    {x : ι → ℝ} (hx : x ∈ rectangularCell p i) :
    ∃ b : Fin p, ∃ u ∈ gridUnitCell, x=(fun j => ((offsetVector i b.val j:ℤ):ℝ))+u := by
  have _ := hp
  have hxj := (mem_rectangularCell_iff p i x).mp hx
  have hxi : 0 ≤ x i ∧ x i < (p:ℝ) := by simpa using hxj i
  let q : ℤ := ⌊x i⌋
  have hq0 : 0 ≤ q := Int.floor_nonneg.mpr hxi.1
  have hqp : q < (p:ℤ) := Int.floor_lt.mpr hxi.2
  let b : Fin p := ⟨q.toNat,by omega⟩
  have hbq : (b.val:ℤ)=q := Int.toNat_of_nonneg hq0
  let o : ι → ℝ := fun j => ((offsetVector i b.val j:ℤ):ℝ)
  refine ⟨b,x-o,?_,by dsimp [o]; abel⟩
  rw [gridUnitCell,Set.mem_pi]
  intro j hj
  change 0 ≤ x j-o j ∧ x j-o j < 1
  by_cases hji : j=i
  · subst j
    have hoi : o i=(q:ℝ) := by simp [o,offsetVector,hbq]
    rw [hoi]
    have hl := Int.floor_le (x i)
    have hu := Int.lt_floor_add_one (x i)
    change (q:ℝ) ≤ x i at hl
    change x i < (q:ℝ)+1 at hu
    constructor <;> linarith
  · have hoj : o j=0 := by simp [o,offsetVector,Pi.single_eq_of_ne hji]
    rw [hoj,sub_zero]
    simpa [hji] using hxj j

lemma normalizedRectangularCell_subset_offsetCells (p : ℕ) (hp : 0 < p) (i : ι) :
    normalizedRectangularCell p hp i ⊆ ⋃ b : Fin p, offsetCell p hp i b := by
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨b,u,hu,he⟩ := rectangularCell_unit_decomposition p hp i hx
  apply Set.mem_iUnion.mpr
  refine ⟨b,?_⟩
  apply Set.mem_image_of_mem
  exact ⟨u,hu,he.symm⟩

lemma modForm_offsetVector (p : ℕ) (i : ι) (a : ι → ℤ) (b : ℤ) :
    modForm p i a (offsetVector i b)=(b:ZMod p) := by
  change ((offsetVector i b i:ℤ):ZMod p)+∑ j ∈ Finset.univ.erase i,
    (a j:ZMod p)*((offsetVector i b j:ℤ):ZMod p)=_
  have hs : ∑ j ∈ Finset.univ.erase i, (a j:ZMod p)*((offsetVector i b j:ℤ):ZMod p)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [offsetVector,Pi.single_eq_of_ne (Finset.mem_erase.mp hj).1]
  rw [hs,add_zero]
  simp [offsetVector]



lemma offsetCell_hit (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ)
    (S : Finset (ι → ℤ)) {J : Set (ι → ℝ)}
    (hthick : ∀ z ∈ S, ∀ u ∈ gridUnitCell, gridMap p hp z + normalizeEquiv p hp u ∈ J)
    (b : Fin p) (hb : ∃ z ∈ S, modForm p i a z=(b.val:ZMod p))
    {x : ι → ℝ} (hx : x ∈ offsetCell p hp i b) :
    ∃ l : normalized p hp i a, x+l ∈ J := by
  obtain ⟨z,hz,hzb⟩ := hb
  obtain ⟨y,⟨u,hu,rfl⟩,rfl⟩ := hx
  let w := z-offsetVector i b.val
  have hw : gridMap p hp w ∈ normalized p hp i a := by
    rw [grid_mem_normalized_iff]
    dsimp [w]
    rw [map_sub,modForm_offsetVector,hzb]
    simp
  refine ⟨⟨gridMap p hp w,hw⟩,?_⟩
  have hh := hthick z hz u hu
  convert hh using 1
  change normalizeEquiv p hp ((fun j => ((offsetVector i b.val j:ℤ):ℝ))+u)+
    normalizeEquiv p hp (fun j => (w j:ℝ)) =
      normalizeEquiv p hp (fun j => (z j:ℝ))+normalizeEquiv p hp u
  rw [←map_add,←map_add]
  apply congrArg (normalizeEquiv p hp)
  ext j
  simp only [Pi.add_apply,w,Pi.sub_apply,Int.cast_sub]
  ring


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def badOffsets (p : ℕ) (i : ι) (a : ι → ℤ) (S : Finset (ι → ℤ)) : Finset (Fin p) := by
  classical
  exact Finset.univ.filter (fun b => ∀ z ∈ S, modForm p i a z ≠ (b.val:ZMod p))

lemma cell_hole_le_badOffsets (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ)
    (S : Finset (ι → ℤ)) {J : Set (ι → ℝ)}
    (hthick : ∀ z ∈ S, ∀ u ∈ gridUnitCell, gridMap p hp z + normalizeEquiv p hp u ∈ J) :
    volume (normalizedRectangularCell p hp i ∩ {x | ∀ l : normalized p hp i a, x+l ∉ J}) ≤
      ((badOffsets p i a S).card:ℝ≥0∞)/(p:ℝ≥0∞) := by
  classical
  have hsub : normalizedRectangularCell p hp i ∩ {x | ∀ l : normalized p hp i a, x+l ∉ J} ⊆
      ⋃ b ∈ badOffsets p i a S, offsetCell p hp i b := by
    rintro x ⟨hx,hmiss⟩
    obtain ⟨b,hb⟩ := Set.mem_iUnion.mp (normalizedRectangularCell_subset_offsetCells p hp i hx)
    have hbad : b ∈ badOffsets p i a S := by
      simp only [badOffsets,Finset.mem_filter,Finset.mem_univ,true_and]
      intro z hz hzb
      obtain ⟨l,hl⟩ := offsetCell_hit p hp i a S hthick b ⟨z,hz,hzb⟩ hb
      exact hmiss l hl
    exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨hbad,hb⟩⟩
  calc
    _ ≤ volume (⋃ b ∈ badOffsets p i a S, offsetCell p hp i b) := measure_mono hsub
    _ ≤ ∑ b ∈ badOffsets p i a S, volume (offsetCell p hp i b) := measure_biUnion_finset_le _ _
    _ = _ := by simp [volume_offsetCell,div_eq_mul_inv]

end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.RogersPreparation
open Horizontal Completion Set MeasureTheory
open scoped Pointwise ENNReal

lemma pointCount_zero_iff_no_hit {d : ℕ} (L : FullLattice d)
    (J : Set (Fin d → ℝ)) (x : Fin d → ℝ) :
    pointCount L J x=0 ↔ ∀ l : L.module, x+l ∉ J := by
  classical
  simp only [pointCount,periodize,ENNReal.tsum_eq_zero]
  apply forall_congr'
  intro l
  by_cases h : x+l ∈ J <;> simp [h]



lemma hole_eq_unit_fundamental_hole {d : ℕ} (L : FullLattice d)
    {J F : Set (Fin d → ℝ)} (hJ : IsCompact J)
    (hF : IsAddFundamentalDomain L.module F volume) (hvol : volume F=1) :
    L.hole J=volume (F ∩ {x | ∀ l : L.module, x+l ∉ J}) := by
  let H : Set (Fin d → ℝ) := {x | pointCount L J x=0}
  have hH : MeasurableSet H := (measurable_periodize L (measurable_one.indicator hJ.measurableSet)) (.singleton 0)
  have hperiodic (l : L.module) : (fun x => (l:Fin d → ℝ)+x) ⁻¹' H=H := by
    ext x
    change pointCount L J ((l:Fin d → ℝ)+x)=0 ↔ pointCount L J x=0
    rw [pointCount_eq_zero,pointCount_eq_zero,map_add,
      (latticeProjection_eq_zero_iff L.module _).mpr l.property,zero_add]
  have hv : volume (cell L)=1 := (cell_fundamental L).measure_eq hF |>.trans hvol
  rw [hole_eq_zero_count_probability L hJ,translateLaw,hv,inv_one,one_smul,
    Measure.restrict_apply hH]
  change volume (H ∩ cell L)=_
  rw [(cell_fundamental L).measure_set_eq hF hH hperiodic]
  congr 1
  ext x
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,H,pointCount_zero_iff_no_hit,and_comm]

end SingleLatticeCovering.RogersPreparation

namespace SingleLatticeCovering.PrimeKernel
open RogersPreparation Horizontal Set MeasureTheory
open scoped Pointwise ENNReal
variable {d : ℕ}

def normalizedFull (p : ℕ) (hp : 0 < p) (i : Fin d) (a : Fin d → ℤ) : FullLattice d :=
  ⟨normalized p hp i a,inferInstance,inferInstance⟩

lemma normalizedFull_hole_le_badOffsets (p : ℕ) (hp : 0 < p) (i : Fin d) (a : Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    (hthick : ∀ z ∈ S, ∀ u ∈ gridUnitCell, gridMap p hp z + normalizeEquiv p hp u ∈ J) :
    (normalizedFull p hp i a).hole J ≤ ((badOffsets p i a S).card:ℝ≥0∞)/(p:ℝ≥0∞) := by
  rw [hole_eq_unit_fundamental_hole (normalizedFull p hp i a) hJ
    (normalizedRectangularCell_fundamental p hp i a) (volume_normalizedRectangularCell p hp i)]
  exact cell_hole_le_badOffsets p hp i a S hthick

end SingleLatticeCovering.PrimeKernel


noncomputable section
namespace SingleLatticeCovering.AffineVoid
open scoped BigOperators
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {n : ℕ} {σ : Type*} [Fintype σ]

def normalDual (c : Kˣ) (b : K) (a : Fin n → K) : Fin (n+2) → K :=
  Fin.cons (-(c:K)*b) (Fin.cons (c:K) (fun j => (c:K)*a j))

def fullMiss (v : σ → Fin (n+1) → K) (w : Fin (n+2) → K) : ℝ := by
  classical
  exact if ∀ i, (∑ j, w j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j) ≠ 0 then 1 else 0

def normalizedMiss (v : σ → Fin (n+1) → K) (a : Fin n → K) (b : K) : ℝ := by
  classical
  exact if ∀ i, v i 0 + ∑ j, a j*v i j.succ ≠ b then 1 else 0

lemma fullMiss_nonneg {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n : ℕ} {σ : Type*} [Fintype σ] (v : σ → Fin (n+1) → K) (w : Fin (n+2) → K) :
    0 ≤ fullMiss v w := by
  classical
  unfold fullMiss
  split_ifs <;> norm_num
lemma normalizedMiss_nonneg {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n : ℕ} {σ : Type*} [Fintype σ] (v : σ → Fin (n+1) → K) (a : Fin n → K) (b : K) :
    0 ≤ normalizedMiss v a b := by
  classical
  unfold normalizedMiss
  split_ifs <;> norm_num

lemma normalDual_injective {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n : ℕ} : Function.Injective
    (fun t : Kˣ × K × (Fin n → K) => normalDual t.1 t.2.1 t.2.2) := by
  rintro ⟨c,b,a⟩ ⟨c',b',a'⟩ he
  have hc : (c:K)=(c':K) := by
    have h := congrFun he ((0:Fin (n+1)).succ)
    simpa [normalDual] using h
  have hcc : c=c' := Units.ext hc
  subst c'
  have hb : b=b' := by
    have h := congrFun he 0
    simp only [normalDual,Fin.cons_zero] at h
    exact mul_left_cancel₀ (neg_ne_zero.mpr c.ne_zero) h
  have ha : a=a' := by
    funext j
    have h := congrFun he j.succ.succ
    simp only [normalDual,Fin.cons_succ] at h
    exact mul_left_cancel₀ c.ne_zero h
  subst b'; subst a'; rfl

lemma normalDual_dot {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n : ℕ} (c : Kˣ) (b : K) (a : Fin n → K) (z : Fin (n+1) → K) :
    (∑ j, normalDual c b a j * (Fin.cons (1:K) z : Fin (n+2) → K) j) =
      (c:K)*(z 0+∑ j, a j*z j.succ-b) := by
  simp only [normalDual,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_one]
  rw [mul_sub,mul_add,Finset.mul_sum]
  ring_nf

lemma fullMiss_normalDual (v : σ → Fin (n+1) → K) (c : Kˣ) (b : K) (a : Fin n → K) :
    fullMiss v (normalDual c b a)=normalizedMiss v a b := by
  classical
  unfold fullMiss normalizedMiss
  have he : (∀ i, (∑ j, normalDual c b a j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j) ≠ 0) ↔
      (∀ i, v i 0+∑ j, a j*v i j.succ ≠ b) := by
    apply forall_congr'
    intro i
    rw [normalDual_dot]
    exact ⟨fun h => sub_ne_zero.mp (mul_ne_zero_iff.mp h).2,
      fun h => mul_ne_zero c.ne_zero (sub_ne_zero.mpr h)⟩
  simp only [he]



lemma raw_conditioning_bound (v : σ → Fin (n+1) → K) :
    (Fintype.card Kˣ:ℝ)*(∑ a : Fin n → K, ∑ b : K, normalizedMiss v a b) ≤
      ∑ w : Fin (n+2) → K, fullMiss v w := by
  classical
  let f := fun t : Kˣ × K × (Fin n → K) => normalDual t.1 t.2.1 t.2.2
  have hs : (∑ t, fullMiss v (f t)) ≤ ∑ w, fullMiss v w := by
    rw [←Finset.sum_image (fun x hx y hy he => normalDual_injective he)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun w hw hwt => fullMiss_nonneg v w)
  have he : (∑ t, fullMiss v (f t)) =
      (Fintype.card Kˣ:ℝ)*(∑ a : Fin n → K, ∑ b : K, normalizedMiss v a b) := by
    simp only [f,Fintype.sum_prod_type,fullMiss_normalDual]
    rw [Finset.sum_const,nsmul_eq_mul]
    congr 1
    exact Finset.sum_comm
  rwa [he] at hs

def meanFull (v : σ → Fin (n+1) → K) : ℝ :=
  (∑ w : Fin (n+2) → K, fullMiss v w)/(Fintype.card K:ℝ)^(n+2)
def meanNormalized (v : σ → Fin (n+1) → K) : ℝ :=
  (∑ a : Fin n → K, ∑ b : K, normalizedMiss v a b)/(Fintype.card K:ℝ)^(n+1)

lemma conditioning_bound (v : σ → Fin (n+1) → K) :
    meanNormalized v ≤ ((Fintype.card K:ℝ)/((Fintype.card K:ℝ)-1))*meanFull v := by
  have hcard : 1 < Fintype.card K := Fintype.one_lt_card
  have hc : (1:ℝ) < Fintype.card K := by exact_mod_cast hcard
  have hc0 : (0:ℝ) < Fintype.card K := by linarith
  have hcm : (0:ℝ) < (Fintype.card K:ℝ)-1 := by linarith
  have hh := raw_conditioning_bound v
  rw [Fintype.card_units,Nat.cast_sub (by omega),Nat.cast_one] at hh
  unfold meanNormalized meanFull
  apply (div_le_iff₀ (pow_pos hc0 _)).mpr
  calc
    _ ≤ (∑ w : Fin (n+2) → K, fullMiss v w)/((Fintype.card K:ℝ)-1) :=
      (le_div_iff₀ hcm).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by
      rw [show (Fintype.card K:ℝ)^(n+2)=(Fintype.card K:ℝ)^(n+1)*(Fintype.card K:ℝ) by rw [show n+2=(n+1)+1 by omega,pow_succ]]
      field_simp [hc0.ne',hcm.ne']


end SingleLatticeCovering.AffineVoid


noncomputable section
namespace SingleLatticeCovering.ConvexCore
open Set MeasureTheory Filter Topology Metric
open scoped Pointwise ENNReal
variable {d : ℕ}

lemma interior_nonempty_of_volume_pos {J : Set (Fin d → ℝ)}
    (hconv : Convex ℝ J) (hV : 0 < volume.real J) : (interior J).Nonempty := by
  by_contra hh
  have hi : interior J = ∅ := Set.not_nonempty_iff_eq_empty.mp hh
  have hs : J ⊆ frontier J := by
    rw [frontier,hi,sdiff_empty]
    exact subset_closure
  have hz : volume J = 0 := measure_mono_null hs (hconv.addHaar_frontier volume)
  simp only [measureReal_def,hz,ENNReal.toReal_zero] at hV
  exact lt_irrefl _ hV

lemma core_subset_interior {J : Set (Fin d → ℝ)} (hconv : Convex ℝ J)
    (h0 : 0 ∈ interior J) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    c • J ⊆ interior J := by
  rintro x ⟨y,hy,rfl⟩
  simpa only [smul_zero,zero_add] using
    hconv.combo_interior_self_mem_interior h0 hy (sub_pos.mpr hc1) hc0 (sub_add_cancel 1 c)

lemma core_compact {J : Set (Fin d → ℝ)} (hJ : IsCompact J) (c : ℝ) :
    IsCompact (c • J) := by
  exact hJ.image (by fun_prop)

lemma core_volume {J : Set (Fin d → ℝ)} {c : ℝ} (hc : 0 ≤ c) :
    volume.real (c • J)=c^d*volume.real J := by
  rw [measureReal_def,Measure.addHaar_smul_of_nonneg volume hc,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hc _)]
  simp only [Module.finrank_pi,Fintype.card_fin]
  rfl

lemma compact_uniform_add {J C : Set (Fin d → ℝ)} (hC : IsCompact C)
    (hsub : C ⊆ interior J) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ C, ∀ u : Fin d → ℝ, ‖u‖ ≤ δ → x+u ∈ J := by
  obtain ⟨δ,hδ,hs⟩ := hC.exists_cthickening_subset_open isOpen_interior hsub
  refine ⟨δ,hδ,fun x hx u hu => interior_subset (hs ?_)⟩
  apply Metric.mem_cthickening_of_dist_le (x+u) x δ C hx
  simpa only [dist_eq_norm,add_sub_cancel_left] using hu

lemma exists_shrink_exp {V ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ Real.exp (-(c^d*V)) < Real.exp (-V)+ε := by
  have hc : ContinuousAt (fun c : ℝ => Real.exp (-(c^d*V))) 1 := by fun_prop
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc ε hε
  let t := min (δ/2) (1/2:ℝ)
  have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨1-t,by linarith,by linarith,?_⟩
  have hh := hclose (show dist (1-t) 1 < δ by
    simpa only [Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos ht] using htδ)
  simp only [one_pow,one_mul,Real.dist_eq] at hh
  linarith [(abs_lt.mp hh).2]

end SingleLatticeCovering.ConvexCore


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
