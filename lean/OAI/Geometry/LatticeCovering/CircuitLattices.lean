import OAI.Geometry.LatticeCovering.CircuitVolumes

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

namespace SingleLatticeCovering.CircuitArithmetic
open Module Submodule MeasureTheory
open scoped BigOperators Pointwise

abbrev integerLattice (r : ℕ) : Submodule ℤ (Fin r → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin r)))

def integerCoordinates (r : ℕ) : integerLattice r ≃ₗ[ℤ] (Fin r → ℤ) :=
  ((Pi.basisFun ℝ (Fin r)).restrictScalars ℤ).equivFun

lemma integerCoordinates_cast {r : ℕ} (x : integerLattice r) (i : Fin r) :
    ((integerCoordinates r x i : ℤ) : ℝ) = (x : Fin r → ℝ) i := by
  have h := (Pi.basisFun ℝ (Fin r)).restrictScalars_repr_apply ℤ x i
  simpa [integerCoordinates] using h

lemma integerLattice_covolume (r : ℕ) : ZLattice.covolume (integerLattice r) = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin r)) volume),
    ZSpan.fundamentalDomain_pi_basisFun]
  simp [measureReal_def, volume_pi, Measure.pi_pi, Real.volume_Ico]


def congruenceKernel {r q : ℕ} (A : integerLattice r →ₗ[ℤ] ZMod q) :
    Submodule ℤ (Fin r → ℝ) := (LinearMap.ker A).map (integerLattice r).subtype

lemma congruenceKernel_le {r q : ℕ} (A : integerLattice r →ₗ[ℤ] ZMod q) :
    congruenceKernel A ≤ integerLattice r := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

instance congruenceKernel_discrete {r q : ℕ} (A : integerLattice r →ₗ[ℤ] ZMod q) :
    DiscreteTopology (congruenceKernel A) :=
  DiscreteTopology.of_subset (inferInstance : DiscreteTopology (integerLattice r))
    (congruenceKernel_le A)

lemma mem_congruenceKernel_iff {r q : ℕ} (A : integerLattice r →ₗ[ℤ] ZMod q)
    (x : integerLattice r) :
    (x : Fin r → ℝ) ∈ congruenceKernel A ↔ A x = 0 := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    have : y=x := Subtype.ext hxy
    subst y
    exact hy
  · intro h
    exact ⟨x,h,rfl⟩

instance congruenceKernel_full {r q : ℕ} [NeZero q]
    (A : integerLattice r →ₗ[ℤ] ZMod q) : IsZLattice ℝ (congruenceKernel A) where
  span_top := by
    apply top_unique
    rw [←(Pi.basisFun ℝ (Fin r)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    let z := (Pi.basisFun ℝ (Fin r)).restrictScalars ℤ i
    have hz : (q:ℤ) • (z : Fin r → ℝ) ∈ congruenceKernel A := by
      apply (mem_congruenceKernel_iff A ((q:ℤ) • z)).mpr
      rw [map_smul]
      simp
    have hh := (Submodule.span ℝ (congruenceKernel A : Set (Fin r → ℝ))).smul_mem
      ((q:ℝ)⁻¹) (Submodule.subset_span hz)
    have hq : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    have he : (q:ℝ)⁻¹ • ((q:ℤ) • (z : Fin r → ℝ)) = (Pi.basisFun ℝ (Fin r)) i := by
      ext j
      simp [z, hq]
    rwa [he] at hh

lemma congruenceKernel_relIndex {r q : ℕ}
    (A : integerLattice r →ₗ[ℤ] ZMod q) :
    (congruenceKernel A).toAddSubgroup.relIndex (integerLattice r).toAddSubgroup =
      A.toAddMonoidHom.ker.index := by
  have he : (congruenceKernel A).toAddSubgroup.comap (integerLattice r).toAddSubgroup.subtype =
      A.toAddMonoidHom.ker := by
    ext x
    exact mem_congruenceKernel_iff A x
  change ((congruenceKernel A).toAddSubgroup.comap (integerLattice r).toAddSubgroup.subtype).index = _
  rw [he]



theorem congruenceKernel_covolume {r q : ℕ} [NeZero q]
    (A : integerLattice r →ₗ[ℤ] ZMod q) (hA : Function.Surjective A) :
    ZLattice.covolume (congruenceKernel A) = q := by
  classical
  have h := ZLattice.covolume_div_covolume_eq_relIndex
    (congruenceKernel A) (integerLattice r) (congruenceKernel_le A)
  rw [integerLattice_covolume, div_one, congruenceKernel_relIndex] at h
  have hi : A.toAddMonoidHom.ker.index = q := by
    rw [AddSubgroup.index_ker]
    have hr : A.toAddMonoidHom.range = ⊤ := AddMonoidHom.range_eq_top.mpr hA
    rw [hr, Nat.card_eq_fintype_card]
    simp
  simpa [hi] using h


def relationForm {r : ℕ} (q : ℕ) (a : Fin r → ℤ) :
    integerLattice r →ₗ[ℤ] ZMod q where
  toFun x := ∑ i, (a i : ZMod q) * (integerCoordinates r x i : ZMod q)
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [map_smul, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul, RingHom.id_apply,
      Finset.mul_sum, Int.cast_id]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma relationForm_surjective {r q : ℕ} (a : Fin r → ℤ)
    (h : ∃ z : Fin r → ℤ, (∑ i, a i*z i : ZMod q) = 1) :
    Function.Surjective (relationForm q a) := by
  obtain ⟨z,hz⟩ := h
  have hone : relationForm q a ((integerCoordinates r).symm z) = 1 := by
    simpa [relationForm] using hz
  intro c
  obtain ⟨k,hk⟩ := ZMod.intCast_surjective c
  refine ⟨k • (integerCoordinates r).symm z,?_⟩
  rw [map_smul, hone]
  simpa using hk



lemma primitive_relation_surjective {r : ℕ} (a : Fin (r+1) → ℤ)
    (ha : Finset.univ.gcd a = 1) :
    Function.Surjective (relationForm (a 0).natAbs (fun i => a i.succ)) := by
  apply relationForm_surjective
  obtain ⟨z,hz⟩ := Finset.gcd_eq_sum_mul Finset.univ a
  rw [ha, Fin.sum_univ_succ] at hz
  refine ⟨fun i => z i.succ,?_⟩
  have hcast := congrArg (fun t : ℤ => (t : ZMod (a 0).natAbs)) hz
  have hzero : (a 0 : ZMod (a 0).natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natAbs_dvd.mpr (dvd_refl (a 0))
  simpa [Int.cast_add, Int.cast_mul, Int.cast_sum, hzero] using hcast.symm

lemma primitive_relation_covolume {r : ℕ} (a : Fin (r+1) → ℤ)
    (hzero : a 0 ≠ 0) (ha : Finset.univ.gcd a = 1) :
    ZLattice.covolume (congruenceKernel (relationForm (a 0).natAbs (fun i => a i.succ))) =
      |(a 0 : ℝ)| := by
  let : NeZero (a 0).natAbs := ⟨Int.natAbs_ne_zero.mpr hzero⟩
  rw [congruenceKernel_covolume _ (primitive_relation_surjective a ha)]
  simp

end SingleLatticeCovering.CircuitArithmetic

namespace SingleLatticeCovering.CircuitGrid
open Module Submodule MeasureTheory CircuitPacking CircuitArithmetic
open scoped BigOperators


lemma exists_column_basis {r : ℕ} {κ : Type*} [Finite κ]
    (v : κ → (Fin r → ℝ)) (hv : Submodule.span ℝ (Set.range v) = ⊤) :
    ∃ b : Basis (Fin r) ℝ (Fin r → ℝ), ∀ i, ∃ j, b i = v j := by
  classical
  obtain ⟨ι,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ v
  let : Finite ι := Finite.of_injective a ha
  let : Fintype ι := Fintype.ofFinite ι
  let b : Basis ι ℝ (Fin r → ℝ) := Basis.mk hli (by rw [hspan,hv])
  have hc : Fintype.card ι = r := by
    rw [←Module.finrank_eq_card_basis b, Module.finrank_pi, Fintype.card_fin]
  let e : ι ≃ Fin r := Fintype.equivOfCardEq (by simpa using hc)
  refine ⟨b.reindex e, fun i => ⟨a (e.symm i), ?_⟩⟩
  simp [b, Basis.reindex_apply, Basis.coe_mk]

lemma count_of_spanning_columns {r : ℕ} {κ : Type*} [Finite κ]
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : κ → L) (hv : Submodule.span ℝ (Set.range (fun j => (v j : Fin r → ℝ))) = ⊤)
    (S : Finset L) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i j, |(v i : Fin r → ℝ) j| ≤ R)
    (hS : ∀ x ∈ S, ∀ j, |(x:Fin r → ℝ) j| ≤ R) :
    (S.card : ℝ) * ZLattice.covolume L ≤ (2*(r+1)*R)^r := by
  obtain ⟨b,hb'⟩ := exists_column_basis (fun j => (v j : Fin r → ℝ)) hv
  apply short_basis_lattice_count L b (fun i => ?_) S hR (fun i j => ?_) hS
  · obtain ⟨j,hj⟩ := hb' i
    rw [hj]
    exact (v j).property
  · obtain ⟨k,hk⟩ := hb' i
    rw [hk]
    exact hb k j




theorem array_count_of_spanning_columns {r d : ℕ} {κ : Type*} [Finite κ]
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : κ → L) (hv : Submodule.span ℝ (Set.range (fun j => (v j : Fin r → ℝ))) = ⊤)
    (X : Finset (Fin d → L)) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i j, |(v i : Fin r → ℝ) j| ≤ R)
    (hX : ∀ x ∈ X, ∀ i j, |(x i : Fin r → ℝ) j| ≤ R) :
    (X.card : ℝ) * (ZLattice.covolume L)^d ≤ ((2*(r+1)*R)^r)^d := by
  classical
  let S : Finset L := X.biUnion (fun x => Finset.univ.image x)
  have hS : ∀ x ∈ S, ∀ j, |(x : Fin r → ℝ) j| ≤ R := by
    intro x hx
    obtain ⟨z,hz,hxz⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hxz
    exact hX z hz i
  have hXS : X ⊆ Fintype.piFinset (fun _ : Fin d => S) := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hcard : (X.card : ℝ) ≤ (S.card : ℝ)^d := by
    have hc : X.card ≤ S.card^d := by
      simpa using (Finset.card_le_card hXS)
    exact_mod_cast hc
  have hp := count_of_spanning_columns L v hv S hR hb hS
  have hcpos : 0 ≤ ZLattice.covolume L := (ZLattice.covolume_pos L volume).le
  calc
    (X.card : ℝ)*ZLattice.covolume L^d ≤ (S.card:ℝ)^d*ZLattice.covolume L^d :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg hcpos d)
    _ = ((S.card:ℝ)*ZLattice.covolume L)^d := (mul_pow _ _ _).symm
    _ ≤ ((2*(r+1)*R)^r)^d := pow_le_pow_left₀ (by positivity) hp d


lemma mulVec_surjective_of_rowIndependent {F ι κ : Type*} [Field F]
    [Fintype ι] [Fintype κ] (W : Matrix κ ι F)
    (hW : LinearIndependent F W.row) : Function.Surjective W.mulVec := by
  classical
  have hf : Function.Injective W.vecMulLinear := Matrix.vecMul_injective_iff.mpr hW
  intro b
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective hf
    ((dotProductBilin F F) b)
  refine ⟨fun j => g (Pi.single j 1), ?_⟩
  ext i
  have hi := DFunLike.congr_fun hg (Pi.single i 1)
  have hrow : W.vecMulLinear (Pi.single i 1) = W i := by
    ext j
    simp [Matrix.vecMulLinear, Matrix.vecMul, dotProduct, Pi.single_apply]
  change g (W.vecMulLinear (Pi.single i 1)) = _ at hi
  rw [hrow] at hi
  have hsingle (x : ι) : (fun j => if x=j then (1 : F) else 0) = Pi.single x 1 := by
    funext j
    simp [Pi.single_apply,eq_comm]
  have hgi := LinearMap.pi_apply_eq_sum_univ g (W i)
  simp_rw [hsingle] at hgi
  simpa [Matrix.mulVec, dotProduct, dotProductBilin, Pi.single_apply, mul_comm, eq_comm] using hgi.symm.trans hi



def affineRows {r d : ℕ} (x : Fin r → Fin d → ℤ) : Matrix (Fin r) (Fin (d+1)) ℝ :=
  fun i => Fin.cons 1 (fun j => (x i j : ℝ))

lemma span_affine_columns {r d : ℕ} (x : Fin r → Fin d → ℤ)
    (hx : LinearIndependent ℝ (affineRows x).row) :
    Submodule.span ℝ (Set.range (affineRows x).col) = ⊤ := by
  rw [←Matrix.range_mulVecLin]
  exact LinearMap.range_eq_top.mpr (mulVec_surjective_of_rowIndependent _ hx)

lemma integer_array_count {r d : ℕ} {κ : Type*} [Finite κ]
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : κ → L) (hv : Submodule.span ℝ (Set.range (fun j => (v j : Fin r → ℝ))) = ⊤)
    (X : Finset (Fin r → Fin d → ℤ)) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i j, |(v i : Fin r → ℝ) j| ≤ R)
    (hX : ∀ x ∈ X, ∀ i j, |(x i j : ℝ)| ≤ R)
    (hL : ∀ x ∈ X, ∀ j, (fun i => (x i j : ℝ)) ∈ L) :
    (X.card : ℝ) * (ZLattice.covolume L)^d ≤ ((2*(r+1)*R)^r)^d := by
  classical
  let f : {x // x ∈ X} → Fin d → L := fun x j => ⟨fun i => (x.val i j : ℝ), hL x.val x.property j⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i j
    have hh := congrFun (congrArg (fun z : L => (z : Fin r → ℝ)) (congrFun h j)) i
    exact Int.cast_injective hh
  let Y : Finset (Fin d → L) := X.attach.image f
  have hc : Y.card = X.card := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_attach]
  have hy : ∀ y ∈ Y, ∀ i j, |(y i : Fin r → ℝ) j| ≤ R := by
    intro y hy
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hy
    exact fun i j => hX x.val x.property j i
  have h := array_count_of_spanning_columns L v hv Y hR hb hy
  simpa only [hc] using h



theorem integer_affine_grid_count {r d : ℕ}
    (L : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (X : Finset (Fin r → Fin d → ℤ)) {R : ℝ} (hR : 1 ≤ R)
    (hX : ∀ x ∈ X, ∀ i j, |(x i j : ℝ)| ≤ R)
    (hL : ∀ x ∈ X, ∀ j, (fun i => (x i j : ℝ)) ∈ L)
    (hone : (fun _ : Fin r => (1:ℝ)) ∈ L)
    (hind : ∀ x ∈ X, LinearIndependent ℝ (affineRows x).row) :
    (X.card : ℝ) * (ZLattice.covolume L)^d ≤ ((2*(r+1)*R)^r)^d := by
  classical
  by_cases hn : X.Nonempty
  · obtain ⟨x,hx⟩ := hn
    have hcol (j : Fin (d+1)) : (affineRows x).col j ∈ L := by
      refine Fin.cases ?_ (fun j => ?_) j
      · have he : (affineRows x).col 0 = (fun _ : Fin r => (1:ℝ)) := by ext i; rfl
        rw [he]
        exact hone
      · have he : (affineRows x).col j.succ = (fun i : Fin r => (x i j : ℝ)) := by ext i; rfl
        rw [he]
        exact hL x hx j
    let v : Fin (d+1) → L := fun j => ⟨(affineRows x).col j, hcol j⟩
    apply integer_array_count L v (span_affine_columns x (hind x hx)) X (by linarith) ?_ hX hL
    intro j i
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [v, affineRows, Matrix.col, Matrix.transpose] using hR
    · simpa [v, affineRows, Matrix.col, Matrix.transpose] using hX x hx i j
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity

lemma relation_zero_mod {r : ℕ} (a w : Fin (r+1) → ℤ)
    (h : ∑ i, a i*w i = 0) :
    (∑ i : Fin r, (a i.succ : ZMod (a 0).natAbs) * (w i.succ : ZMod (a 0).natAbs)) = 0 := by
  have hcast := congrArg (fun t : ℤ => (t : ZMod (a 0).natAbs)) h
  have hzero : (a 0 : ZMod (a 0).natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natAbs_dvd.mpr (dvd_refl (a 0))
  simpa [Fin.sum_univ_succ, Int.cast_add, Int.cast_mul, Int.cast_sum, hzero] using hcast

lemma projected_relation_mem {r : ℕ} (a w : Fin (r+1) → ℤ)
    (h : ∑ i, a i*w i = 0) :
    (fun i : Fin r => (w i.succ : ℝ)) ∈
      congruenceKernel (relationForm (a 0).natAbs (fun i => a i.succ)) := by
  let z : integerLattice r := (integerCoordinates r).symm (fun i => w i.succ)
  have he : (z : Fin r → ℝ) = (fun i => (w i.succ : ℝ)) := by
    ext i
    rw [←integerCoordinates_cast]
    simp [z]
  rw [←he, mem_congruenceKernel_iff]
  simpa [relationForm, z] using relation_zero_mod a w h





theorem full_circuit_grid_bound {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha0 : a 0 ≠ 0) (hprim : Finset.univ.gcd a = 1) (haff : ∑ i, a i = 0)
    (X : Finset (Fin (r+1) → Fin d → ℤ)) {R : ℝ} (hR : 1 ≤ R)
    (hX : ∀ x ∈ X, ∀ i j, |(x i j : ℝ)| ≤ R)
    (hrel : ∀ x ∈ X, ∀ j, ∑ i, a i*x i j = 0)
    (hind : ∀ x ∈ X, LinearIndependent ℝ (affineRows (fun i => x i.succ)).row) :
    (X.card : ℝ) * |(a 0:ℝ)|^d ≤ ((2*(r+1)*R)^r)^d := by
  classical
  let : NeZero (a 0).natAbs := ⟨Int.natAbs_ne_zero.mpr ha0⟩
  let L := congruenceKernel (relationForm (a 0).natAbs (fun i => a i.succ))
  let tail : (Fin (r+1) → Fin d → ℤ) → (Fin r → Fin d → ℤ) := fun x i => x i.succ
  let Y := X.image tail
  have htail : Set.InjOn tail (X : Set (Fin (r+1) → Fin d → ℤ)) := by
    intro x hx y hy hxy
    funext i j
    refine Fin.cases ?_ (fun i => congrFun (congrFun hxy i) j) i
    have hxj := hrel x hx j
    have hyj := hrel y hy j
    rw [Fin.sum_univ_succ] at hxj hyj
    have hs : (∑ i : Fin r, a i.succ*x i.succ j) = ∑ i : Fin r, a i.succ*y i.succ j := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : ℤ => a i.succ*z) (congrFun (congrFun hxy i) j)
    rw [hs] at hxj
    apply mul_left_cancel₀ ha0
    linarith
  have hc : Y.card = X.card := Finset.card_image_iff.mpr htail
  have hybound : ∀ y ∈ Y, ∀ i j, |(y i j:ℝ)| ≤ R := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact fun i j => hX x hx i.succ j
  have hyL : ∀ y ∈ Y, ∀ j, (fun i => (y i j:ℝ)) ∈ L := by
    intro y hy j
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact projected_relation_mem a (fun i => x i j) (hrel x hx j)
  have hone : (fun _ : Fin r => (1:ℝ)) ∈ L := by
    simpa using projected_relation_mem a (fun _ => 1) (by simpa using haff)
  have hyind : ∀ y ∈ Y, LinearIndependent ℝ (affineRows y).row := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hind x hx
  have h := integer_affine_grid_count L Y hR hybound hyL hone hyind
  rw [hc] at h
  dsimp [L] at h
  rwa [primitive_relation_covolume a ha0 hprim] at h





end SingleLatticeCovering.CircuitGrid

namespace SingleLatticeCovering.CircuitGrid
open Module Submodule MeasureTheory Matrix
open scoped BigOperators Pointwise

lemma gcd_permute {r : ℕ} (a : Fin (r+1) → ℤ) (e : Equiv.Perm (Fin (r+1))) :
    Finset.univ.gcd (fun i => a (e i)) = Finset.univ.gcd a := by
  classical
  change Finset.univ.gcd (a ∘ e) = _
  rw [←Finset.gcd_image, Finset.image_univ_of_surjective e.surjective]



theorem full_circuit_grid_bound_at {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha : ∀ i, a i ≠ 0) (hprim : Finset.univ.gcd a = 1) (haff : ∑ i, a i = 0)
    (X : Finset (Fin (r+1) → Fin d → ℤ)) {R : ℝ} (hR : 1 ≤ R)
    (hX : ∀ x ∈ X, ∀ i j, |(x i j : ℝ)| ≤ R)
    (hrel : ∀ x ∈ X, ∀ j, ∑ i, a i*x i j = 0)
    (hind : ∀ x ∈ X, ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℝ (affineRows (fun i => x (e i.succ))).row)
    (k : Fin (r+1)) :
    (X.card : ℝ) * |(a k:ℝ)|^d ≤ ((2*(r+1)*R)^r)^d := by
  classical
  let e := Equiv.swap (0 : Fin (r+1)) k
  let f : (Fin (r+1) → Fin d → ℤ) → (Fin (r+1) → Fin d → ℤ) := fun x i => x (e i)
  have hf : Function.Injective f := by
    intro x y hxy
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun hxy j
  have hc : (X.image f).card = X.card := Finset.card_image_of_injective X hf
  have hprim' : Finset.univ.gcd (fun i => a (e i)) = 1 := by
    rw [gcd_permute, hprim]
  have hsum : (∑ i, a (e i)) = 0 := (Equiv.sum_comp e a).trans haff
  have hb (x) (hx : x ∈ X.image f) (i j) : |(x i j:ℝ)| ≤ R := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hX y hy (e i) j
  have hrel' (x) (hx : x ∈ X.image f) (j) : ∑ i, a (e i)*x i j = 0 := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact (Equiv.sum_comp e (fun i => a i*y i j)).trans (hrel y hy j)
  have hind' (x) (hx : x ∈ X.image f) :
      LinearIndependent ℝ (affineRows (fun i => x i.succ)).row := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hind y hy e
  have h := full_circuit_grid_bound (fun i => a (e i)) (ha (e 0)) hprim' hsum
    (X.image f) hR hb hrel' hind'
  simpa only [hc, e, Equiv.swap_apply_left] using h


end SingleLatticeCovering.CircuitGrid

noncomputable section
namespace SingleLatticeCovering.CircuitWeight
open scoped BigOperators ENNReal
lemma tsum_int_inv_sq_le_four : (∑' z : ℤ, 1/(z:ℝ)^2) ≤ 4 := by
  have hs : Summable (fun z : ℤ => 1/(z:ℝ)^2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (by intro z; simp) hs]
  have he : (∑' z : ℕ+, 1/((z:ℕ):ℝ)^2) = Real.pi^2/6 := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => 1/(n:ℝ)^2)]
    have hh := hasSum_zeta_two.summable.tsum_eq_zero_add
    simpa only [hasSum_zeta_two.tsum_eq, Nat.cast_zero, zero_pow (by omega : 2 ≠ 0),
      div_zero, zero_add] using hh.symm
  simp only [Int.cast_zero, zero_pow (by omega : 2 ≠ 0), div_zero, zero_add,
    Int.cast_natCast, he, two_smul]
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

lemma int_circuit_weight_le_sq (q : ℝ) (hq : 2 ≤ q) (z : ℤ) :
    |(z:ℝ)|^(-q) ≤ 1/(z:ℝ)^2 := by
  by_cases hz : z = 0
  · simp [hz, Real.zero_rpow (by linarith : -q ≠ 0)]
  have habs : (1:ℝ) ≤ |(z:ℝ)| := by exact_mod_cast Int.one_le_abs hz
  calc
    _ ≤ |(z:ℝ)|^(-(2:ℝ)) := Real.rpow_le_rpow_of_exponent_le habs (by linarith)
    _ = _ := by rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs, one_div]

lemma tsum_ennreal_int_circuit_weight_le (q : ℝ) (hq : 2 ≤ q) :
    (∑' z : ℤ, ENNReal.ofReal (|(z:ℝ)|^(-q))) ≤ 4 := by
  calc
    _ ≤ ∑' z : ℤ, ENNReal.ofReal (1/(z:ℝ)^2) :=
      ENNReal.tsum_le_tsum (fun z => ENNReal.ofReal_le_ofReal (int_circuit_weight_le_sq q hq z))
    _ = ENNReal.ofReal (∑' z : ℤ, 1/(z:ℝ)^2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
        (Real.summable_one_div_int_pow.mpr (by norm_num))).symm
    _ ≤ 4 := by exact_mod_cast ENNReal.ofReal_le_ofReal tsum_int_inv_sq_le_four

lemma tsum_ennreal_fin_prod (r : ℕ) (f : ℤ → ℝ≥0∞) :
    (∑' a : Fin r → ℤ, ∏ j, f (a j)) = (∑' z, f z)^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [←(Fin.consEquiv (fun _ : Fin (r+1) => ℤ)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod (f := fun (z : ℤ) (a : Fin r → ℤ) => f z * ∏ j, f (a j))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ih, ENNReal.tsum_mul_right, pow_succ']



theorem tsum_integerCircuitWeight_le (r : ℕ) (q : ℝ) (hq : 2 ≤ q) :
    (∑' a : Fin r → ℤ, ENNReal.ofReal (∏ j, |(a j:ℝ)|^(-q))) ≤ 4^r := by
  simp_rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)]
  rw [tsum_ennreal_fin_prod r (fun z : ℤ => ENNReal.ofReal (|(z:ℝ)|^(-q)))]
  exact pow_le_pow_left' (tsum_ennreal_int_circuit_weight_le q hq) _




lemma height_weight_le {r d : ℕ} {q : ℝ} (hq : 0 < q)
    (a : Fin (r+1) → ℤ) (ha : ∀ i, a i ≠ 0)
    (hmax : ∀ i, |(a i : ℝ)| ≤ q) :
    q⁻¹^d ≤ ∏ i, |(a i:ℝ)|^(-((d:ℝ)/(r+1:ℕ))) := by
  have he : q⁻¹^d = ∏ _ : Fin (r+1), q^(-((d:ℝ)/(r+1:ℕ))) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ←Real.rpow_natCast, ←Real.rpow_neg_one, ←Real.rpow_mul hq.le,
      ←Real.rpow_natCast, ←Real.rpow_mul hq.le]
    congr 1
    push_cast
    field_simp
  rw [he]
  apply Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg hq.le _)
  intro i _
  exact Real.rpow_le_rpow_of_nonpos (abs_pos.mpr (Int.cast_ne_zero.mpr (ha i)))
    (hmax i) (neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

lemma summable_circuit_weight {r d : ℕ} (hd : 2*(r+1) ≤ d) :
    Summable (fun a : Fin (r+1) → ℤ => ∏ i, |(a i:ℝ)|^(-((d:ℝ)/(r+1:ℕ)))) := by
  have hq : (2:ℝ) ≤ (d:ℝ)/(r+1:ℕ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact_mod_cast hd
  have ht := tsum_integerCircuitWeight_le (r+1) _ hq
  have hn : (∑' a : Fin (r+1) → ℤ, ENNReal.ofReal (∏ i, |(a i:ℝ)|^(-((d:ℝ)/(r+1:ℕ))))) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt ht (by finiteness))
  have hp (a : Fin (r+1) → ℤ) : 0 ≤ ∏ i, |(a i:ℝ)|^(-((d:ℝ)/(r+1:ℕ))) := by positivity
  simpa only [ENNReal.toReal_ofReal (hp _)] using ENNReal.summable_toReal hn



end SingleLatticeCovering.CircuitWeight

namespace SingleLatticeCovering.CircuitGrid
open scoped BigOperators



theorem normalized_circuit_grid_domination {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha : ∀ i, a i ≠ 0) (hprim : Finset.univ.gcd a = 1) (haff : ∑ i, a i = 0)
    (X : Finset (Fin (r+1) → Fin d → ℤ)) {B t : ℝ} (hB : 1 ≤ B) (ht : 1 ≤ t)
    (hX : ∀ x ∈ X, ∀ i j, |(x i j : ℝ)| ≤ B*t)
    (hrel : ∀ x ∈ X, ∀ j, ∑ i, a i*x i j = 0)
    (hind : ∀ x ∈ X, ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℝ (affineRows (fun i => x (e i.succ))).row) :
    (X.card : ℝ) / t^(r*d) ≤ (2*(r+1)*B)^(r*d) *
      ∏ i, |(a i:ℝ)|^(-((d:ℝ)/(r+1:ℕ))) := by
  classical
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |(a i:ℝ)|)
    Finset.univ_nonempty
  have hq : 0 < |(a k:ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (ha k))
  have hBB : 0 ≤ 2*(r+1:ℕ)*B := by positivity
  have htt : 0 < t := by linarith
  have hp := full_circuit_grid_bound_at a ha hprim haff X
    (one_le_mul_of_one_le_of_one_le hB ht) hX hrel hind k
  have hnorm : (X.card:ℝ) / t^(r*d) ≤ (2*(r+1)*B)^(r*d) * |(a k:ℝ)|⁻¹^d := by
    apply (div_le_iff₀ (pow_pos htt _)).mpr
    have hdiv := (le_div_iff₀ (pow_pos hq d)).mpr hp
    calc
      _ ≤ ((2*(r+1)*(B*t))^r)^d / |(a k:ℝ)|^d := hdiv
      _ = (2*(r+1)*B)^(r*d) * |(a k:ℝ)|⁻¹^d * t^(r*d) := by
        rw [←pow_mul, show 2*(r+1)*(B*t) = (2*(r+1)*B)*t by ring, mul_pow]
        rw [inv_pow, div_eq_mul_inv]
        ring
  exact hnorm.trans (mul_le_mul_of_nonneg_left
    (CircuitWeight.height_weight_le hq a ha (fun i => hmax i (Finset.mem_univ i)))
    (by positivity))


end SingleLatticeCovering.CircuitGrid




noncomputable section
namespace SingleLatticeCovering.CircuitLimit
open Filter
open scoped Topology




theorem eventually_tsum_le_of_dominated_comparison {α β : Type*}
    {l : Filter α} [l.NeBot] (f g : α → β → ℝ) (G b : β → ℝ)
    (hb : Summable b) (hb0 : ∀ a, 0 ≤ b a)
    (hg0 : ∀ t a, 0 ≤ g t a) (hG : Summable G)
    (hlim : ∀ a, Tendsto (fun t => g t a) l (𝓝 (G a)))
    (hf : ∀ᶠ t in l, ∀ a, 0 ≤ f t a ∧ f t a ≤ g t a ∧ f t a ≤ b a)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, (∑' a, f t a) < (∑' a, G a)+ε := by
  let H := fun t a => min (g t a) (b a)
  have hH0 (t a) : 0 ≤ H t a := le_min (hg0 t a) (hb0 a)
  have hHbound (t a) : ‖H t a‖ ≤ b a := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hH0 t a)]
    exact min_le_right _ _
  have hHsum (t) : Summable (H t) := hb.of_norm_bounded (hHbound t)
  have hHlim : Tendsto (fun t => ∑' a, H t a) l (𝓝 (∑' a, min (G a) (b a))) :=
    tendsto_tsum_of_dominated_convergence hb (fun a => (hlim a).min tendsto_const_nhds)
      (Eventually.of_forall hHbound)
  have hG0 (a) : 0 ≤ G a := ge_of_tendsto (hlim a) (Eventually.of_forall (fun t => hg0 t a))
  have hminsum : Summable (fun a => min (G a) (b a)) := by
    apply hb.of_norm_bounded
    intro a
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hG0 a) (hb0 a))]
    exact min_le_right _ _
  have hminle : (∑' a, min (G a) (b a)) ≤ ∑' a, G a :=
    hminsum.tsum_le_tsum (fun _ => min_le_left _ _) hG
  filter_upwards [hf,hHlim.eventually (eventually_lt_nhds
    (show (∑' a, min (G a) (b a)) < (∑' a, G a)+ε by linarith))] with t ht hlt
  have hfs : Summable (f t) := hb.of_norm_bounded (fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (ht a).1]
    exact (ht a).2.2)
  exact (hfs.tsum_le_tsum (fun a => le_min (ht a).2.1 (ht a).2.2) (hHsum t)).trans_lt hlt


end SingleLatticeCovering.CircuitLimit


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
