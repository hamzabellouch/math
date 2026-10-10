import OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveSectionDegree

namespace PiExponent.SectionOrderDivisor


variable {X : Scheme.{0}} [IsIntegral X]

abbrev CurvePoint (X : Scheme.{0}) [IsIntegral X] := {x : X // x ≠ genericPoint X}

omit [IsIntegral X] in
theorem mem_zero_support_iff_not_isUnit (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (x : X) : x ∈ (SectionZeroIdeal.zeroIdeal L s).support ↔ ¬ IsUnit (coefficientGermAt L s x) := by
  let F := affineFrameAt L x
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := F.openSet) F.mem,
    SectionZeroIdeal.zeroIdeal_on_frame L s F.openSet F.frame,
    X.zeroLocus_span, X.zeroLocus_singleton]
  apply not_congr
  exact X.toRingedSpace.mem_basicOpen _ x F.mem

def orderAt (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (x : CurvePoint X) : ℕ :=
  letI := hDVR x.1 x.2
  (IsDiscreteValuationRing.addVal (X.presheaf.stalk x.1) (coefficientGermAt L s x.1)).toNat

theorem orderAt_eq_zero_of_not_mem
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (x : CurvePoint X)
    (hx : x.1 ∉ (SectionZeroIdeal.zeroIdeal L s).support) : orderAt hDVR L s x = 0 := by
  let := hDVR x.1 x.2
  have hu : IsUnit (coefficientGermAt L s x.1) :=
    not_not.mp ((mem_zero_support_iff_not_isUnit L s x.1).not.mp hx)
  unfold orderAt
  rw [IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu]
  rfl

def zeroPointEmbedding (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    (SectionZeroIdeal.zeroIdeal L s).subscheme ↪ CurvePoint X where
  toFun y := ⟨(SectionZeroIdeal.zeroIdeal L s).subschemeι y, zeroPoint_ne_generic L s hs y⟩
  inj' _y _z h := (SectionZeroIdeal.zeroIdeal L s).subschemeι.isEmbedding.injective
    (congrArg (fun q : CurvePoint X => (q : X)) h)

theorem orderAt_finite_support
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (hd : topologicalKrullDim X ≤ 1)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    (Function.support (orderAt hDVR L s)).Finite := by
  let : Finite (SectionZeroIdeal.zeroIdeal L s).subscheme :=
    finite_subscheme_of_curve p hd _ (SectionZeroIdeal.zeroIdeal_ne_bot L s hs)
  apply (Set.finite_range (zeroPointEmbedding L s hs)).subset
  intro x hx
  have hmem : x.1 ∈ (SectionZeroIdeal.zeroIdeal L s).support := by
    by_contra hn
    exact hx (orderAt_eq_zero_of_not_mem hDVR L s x hn)
  change x.1 ∈ ((SectionZeroIdeal.zeroIdeal L s).support : Set X) at hmem
  rw [← (SectionZeroIdeal.zeroIdeal L s).range_subschemeι] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, Subtype.ext hy⟩

def divisor
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (hd : topologicalKrullDim X ≤ 1)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) : CurvePoint X →₀ ℕ :=
  Finsupp.ofSupportFinite (orderAt hDVR L s) (orderAt_finite_support p hd hDVR L s hs)

@[simp] theorem divisor_apply
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (hd : topologicalKrullDim X ≤ 1)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (x : CurvePoint X) :
    divisor p hd hDVR L s hs x = orderAt hDVR L s x := rfl

theorem divisor_degree_eq_euler_difference
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (hd : topologicalKrullDim X ≤ 1)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (hfiniteO : ∀ n ≤ 1, letI := Module.compHom (cohomology (structureSheaf X) n) (baseScalars p)
      FiniteDimensional ℂ (cohomology (structureSheaf X) n))
    (hfiniteL : ∀ n ≤ 1, letI := Module.compHom (cohomology L.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology L.sheaf n))
    [Subsingleton (cohomology (structureSheaf X) 2)] :
    (divisor p hd hDVR L s hs).sum (fun _ n => (n : ℤ)) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  classical
  let I := SectionZeroIdeal.zeroIdeal L s
  let : Finite I.subscheme := finite_subscheme_of_curve p hd I
    (SectionZeroIdeal.zeroIdeal_ne_bot L s hs)
  let : Fintype I.subscheme := Fintype.ofFinite _
  let D := divisor p hd hDVR L s hs
  let T := Finset.univ.map (zeroPointEmbedding L s hs)
  have hDT : D.support ⊆ T := by
    intro x hx
    have hn : orderAt hDVR L s x ≠ 0 := by simpa [D] using Finsupp.mem_support_iff.mp hx
    have hm : x.1 ∈ I.support := by
      by_contra hh
      exact hn (orderAt_eq_zero_of_not_mem hDVR L s x hh)
    change x.1 ∈ (I.support : Set X) at hm
    rw [← I.range_subschemeι] at hm
    obtain ⟨y, hy⟩ := hm
    exact Finset.mem_map.mpr ⟨y, Finset.mem_univ y, Subtype.ext hy⟩
  rw [euler_difference_eq_sum_zero_orders p hd L s hs hDVR hfiniteO hfiniteL]
  change D.sum (fun _ n => (n : ℤ)) = _
  rw [D.sum_of_support_subset hDT (fun _ n => (n : ℤ)) (by simp)]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro y _
  rfl

end PiExponent.SectionOrderDivisor

end

end OAI
