import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CoordinateWindowBase
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FullSectorCompatibility
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowSubfamilies
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SmallFamilyGlobal
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SmallControlCalculus

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FullSectorSupport
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_supported (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    SmallSupported (sourceAlignedGroup a r m hm M B.t) (B.fullGeometricSector hlarge P h V) := by
  intro I
  let b := smallAlphabetBalance hlarge I.val (by have hh := I.property.2; omega)
  have hb : b ∉ I.val := smallAlphabetBalance_notMem hlarge I.val _
  rw [B.fullGeometricSector_inclusion hlarge P h I.val I.property.1 b hb (h _ (by have hh := I.property.2; omega) b hb) V hV]
  rintro x ⟨t,rfl⟩
  exact B.geometricSector_aligned I.val b hb P _ V t

theorem constant_small_supported :
    SmallSupported (sourceAlignedGroup a r m hm M B.t)
      (B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))) := by
  intro I
  rw [MonoidHom.comp_assoc,universalMap_spec,← MonoidHom.comp_assoc,← B.initialAlphabet_zero]
  rintro x ⟨t,rfl⟩
  exact B.initialAlphabet_aligned I.val 0 _

theorem fullGeometricSector_small_control (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a) (hVW : V ≤ W) :
    SmallControlled B.c (B.fullGeometricSector hlarge P h V) (B.fullGeometricSector hlarge P h W) := by
  intro I t x hx
  exact B.fullGeometricSector_control hlarge P h V W hVW _ x hx

theorem fullGeometricSector_commute (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hVW : Disjoint V.val W.val)
    (s t : UniversalExtension (alternatingGroup (Fin (m+1)))) :
    Commute (B.fullGeometricSector hlarge P h V s) (B.fullGeometricSector hlarge P h W t) :=
  (B.fullPrimitiveTable hlarge P h).sector_commute (resolvedPolygonMask_disjoint _ hV hVW) s t

end InitialCoverSystem
end FullSectorSupport

section FullWindowCoherence

variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem universal_five_alphabet_hom_ext (hα : 5 ≤ Fintype.card α)
    (f g : UniversalExtension (alternatingGroup α) →* H)
    (h : ∀ I : FiveAlphabet α, f.comp (universalMap (subtypeAlternatingHom I.val)) =
      g.comp (universalMap (subtypeAlternatingHom I.val))) : f = g := by
  have he : (⊤ : Subgroup (UniversalExtension (alternatingGroup α))) ≤ f.eqLocus g := by
    rw [← universal_five_alphabet_generate hα]
    apply iSup_le
    intro I x hx
    obtain ⟨s,rfl⟩ := hx
    exact DFunLike.congr_fun (h I) s
  ext s
  exact he (Subgroup.mem_top s)

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_subfamily (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (v : κ → ι) (hv : P ∘ v = Q)
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (g : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val) :
    B.fullGeometricSector hlarge Q g V = B.fullGeometricSector hlarge P h V := by
  apply universal_five_alphabet_hom_ext (by simp; omega)
  intro I
  let b := smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega)
  have hb : b ∉ I.val := smallAlphabetBalance_notMem hlarge I.val _
  have hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val := by
    subst Q
    intro x y he
    exact hV x y (fun i => he (v i))
  rw [B.fullGeometricSector_inclusion hlarge Q g I.val (by rw [I.property.2]) b hb
      (g _ (by rw [I.property.2]; omega) b hb) V hV,
    B.fullGeometricSector_inclusion hlarge P h I.val (by rw [I.property.2]) b hb
      (h _ (by rw [I.property.2]; omega) b hb) V hV']
  exact B.geometricSector_subfamily I.val b hb P Q v hv _ _ V hV

noncomputable def windowSector (hlarge : 15 < m+1) (n : ℕ)
    (h : B.CoordinateWindowLaw n) (q : Fin 2 → ℤ) (V : polygonAlgebra a) :
    UniversalExtension (alternatingGroup (Fin (m+1))) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (coordinateWindowPrimitives n q) (fun I _ b hb => h I b hb q) V

theorem windowSector_inclusion (hlarge : 15 < m+1) (n k : ℕ)
    (h : B.CoordinateWindowLaw n) (g : B.CoordinateWindowLaw k)
    (q p : Fin 2 → ℤ) (hs : ∀ j, q j ≤ p j) (he : ∀ j, p j+(k:ℤ) ≤ q j+n)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives k p) i).val) V.val) :
    B.windowSector hlarge k g p V = B.windowSector hlarge n h q V :=
  B.fullGeometricSector_subfamily hlarge _ _ (coordinateWindowEmbedding n k q p hs he)
    (coordinateWindowEmbedding_spec n k q p hs he) _ _ V hV

theorem windowSector_overlap_control (hlarge : 15 < m+1) (n k l : ℕ)
    (h : B.CoordinateWindowLaw n) (g : B.CoordinateWindowLaw k) (g' : B.CoordinateWindowLaw l)
    (q p p' : Fin 2 → ℤ)
    (hs : ∀ j, q j ≤ p j) (he : ∀ j, p j+(k:ℤ) ≤ q j+n)
    (hs' : ∀ j, q j ≤ p' j) (he' : ∀ j, p' j+(l:ℤ) ≤ q j+n)
    (V W : polygonAlgebra a) (hVW : V ≤ W)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives k p) i).val) V.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives l p') i).val) W.val) :
    SmallControlled B.c (B.windowSector hlarge k g p V) (B.windowSector hlarge l g' p' W) := by
  rw [B.windowSector_inclusion hlarge n k h g q p hs he V hV,
    B.windowSector_inclusion hlarge n l h g' q p' hs' he' W hW]
  exact B.fullGeometricSector_small_control hlarge _ _ V W hVW

end InitialCoverSystem
end FullWindowCoherence

section AxisWindows

noncomputable def axisWindowPrimitives (j : Fin 2) (k : ℕ) (p : ℤ) :
    Fin (k-1) → Fin 5 × (CutRing × CutRing) := fun i =>
  (coordinateTestIndex j,coordinateShift j (((p+(i.val:ℤ)):CutRing)*cutTau))

theorem axisInterval_resolved {a : ℕ} {r : CutRing} (j : Fin 2) (k : ℕ) (p : ℤ)
    (u v : CutRing) (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j k p) i).val) (coordinateInterval a j u v).val := by
  let A := resolvedAlgebra (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
    (axisWindowPrimitives j k p) i).val)
  have hbetween (s t : ℕ) (hst : s ≤ t) (ht : t < k) :
      coordinateBetween a j (((p+(s:ℤ)):CutRing)*cutTau)
        (((p+(t:ℤ)):CutRing)*cutTau) ∈ A := by
    have hh := coordinate_prefix_generated A j (((p+(s:ℤ)):CutRing)*cutTau) (t-s)
    have he : (((p+(s:ℤ)):CutRing)*cutTau)+((t-s:ℕ):CutRing)*cutTau =
        (((p+(t:ℤ)):CutRing)*cutTau) := by
      push_cast
      rw [Nat.cast_sub hst]
      ring
    rw [he] at hh
    apply hh
    intro i hi
    have hi' : s+i < k-1 := by omega
    have hh := resolved_test (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j k p) z).val) ⟨s+i,hi'⟩
    change (spatialTranslate (coordinateShift j (((p+((s+i:ℕ):ℤ)):CutRing)*cutTau))
      (initialTest a r (coordinateTestIndex j))).val ∈ A at hh
    rw [initialTest_coordinate] at hh
    convert hh using 1
    congr 3
    push_cast
    ring
  have hall (s t : ℕ) (hs : s < k) (ht : t < k) :
      coordinateBetween a j (((p+(s:ℤ)):CutRing)*cutTau)
        (((p+(t:ℤ)):CutRing)*cutTau) ∈ A := by
    by_cases hst : s ≤ t
    · exact hbetween s t hst ht
    · let u' : CutRing := ((p+(s:ℤ)):CutRing)*cutTau
      let v' : CutRing := ((p+(t:ℤ)):CutRing)*cutTau
      by_cases he : Int.fract (ordinary (v'-u')) = 0
      · rw [coordinateBetween_empty j u' v' he]
        exact BooleanSubalgebra.bot_mem
      · have hh := hbetween t s (by omega) hs
        rw [coordinateBetween_reverse j u' v' he] at hh
        simpa only [compl_compl] using BooleanSubalgebra.compl_mem hh
  let s := (endpointLabel u-p).toNat
  let t := (endpointLabel v-p).toNat
  have hs : (s:ℤ) = endpointLabel u-p := Int.toNat_of_nonneg (by omega)
  have ht : (t:ℤ) = endpointLabel v-p := Int.toNat_of_nonneg (by omega)
  have hu' : u = (((p+(s:ℤ)):CutRing)*cutTau)+(u.re:CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [cutTau,hs,endpointLabel]
  have hv' : v = (((p+(t:ℤ)):CutRing)*cutTau)+(v.re:CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [cutTau,ht,endpointLabel]
  change coordinateBetween a j u v ∈ A
  rw [hu',hv',coordinateBetween_period]
  exact hall s t (by omega) (by omega)

def axisWindowEmbedding (j : Fin 2) (n k : ℕ) (q : Fin 2 → ℤ) (p : ℤ)
    (hs : q j ≤ p) (he : p+(k:ℤ) ≤ q j+n) : Fin (k-1) → Fin 2 × Fin (n-1) :=
  fun i => (j,⟨(p-q j).toNat+i.val,by
    have hh : ((p-q j).toNat:ℤ) = p-q j := Int.toNat_of_nonneg (by omega)
    have hi := i.isLt
    omega⟩)

theorem axisWindowEmbedding_spec (j : Fin 2) (n k : ℕ) (q : Fin 2 → ℤ) (p : ℤ)
    (hs : q j ≤ p) (he : p+(k:ℤ) ≤ q j+n) :
    coordinateWindowPrimitives n q ∘ axisWindowEmbedding j n k q p hs he =
      axisWindowPrimitives j k p := by
  funext i
  apply Prod.ext
  · rfl
  · change coordinateShift j (((q j+(((p-q j).toNat+i.val:ℕ):ℤ)):CutRing)*cutTau) = _
    have hh : ((p-q j).toNat:ℤ) = p-q j := Int.toNat_of_nonneg (by omega)
    simp only [Nat.cast_add,hh]
    congr 2
    push_cast
    ring

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem axisFamilyLaw (n : ℕ) (h : B.CoordinateWindowLaw n) (j : Fin 2)
    (k : ℕ) (hk : k ≤ n) (p : ℤ) (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) : B.PrimitiveFamilyLaw I b hb (axisWindowPrimitives j k p) :=
  PrimitiveFamilyLaw.reindex B I b hb (coordinateWindowPrimitives k (fun _ => p))
    (CoordinateWindowLaw.mono B h hk I b hb (fun _ => p)) (fun i => (j,i))

noncomputable def axisSector (hlarge : 15 < m+1) (n : ℕ) (h : B.CoordinateWindowLaw n)
    (j : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (V : polygonAlgebra a) :
    UniversalExtension (alternatingGroup (Fin (m+1))) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (axisWindowPrimitives j k p)
    (fun I _ b hb => B.axisFamilyLaw n h j k hk p I b hb) V

theorem axisSector_in_window (hlarge : 15 < m+1) (n : ℕ) (h : B.CoordinateWindowLaw n)
    (j : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (q : Fin 2 → ℤ)
    (hs : q j ≤ p) (he : p+(k:ℤ) ≤ q j+n) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j k p) i).val) V.val) :
    B.axisSector hlarge n h j k hk p V = B.windowSector hlarge n h q V :=
  B.fullGeometricSector_subfamily hlarge _ _ (axisWindowEmbedding j n k q p hs he)
    (axisWindowEmbedding_spec j n k q p hs he) _ _ V hV

theorem axisSector_overlap_control (hlarge : 15 < m+1) (n : ℕ) (h : B.CoordinateWindowLaw n)
    (j : Fin 2) (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (p q z : ℤ)
    (hsp : z ≤ p) (hep : p+(k:ℤ) ≤ z+n)
    (hsq : z ≤ q) (heq : q+(l:ℤ) ≤ z+n) (V W : polygonAlgebra a) (hVW : V ≤ W)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j k p) i).val) V.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j l q) i).val) W.val) :
    SmallControlled B.c (B.axisSector hlarge n h j k hk p V)
      (B.axisSector hlarge n h j l hl q W) := by
  rw [B.axisSector_in_window hlarge n h j k hk p (fun _ => z) hsp hep V hV,
    B.axisSector_in_window hlarge n h j l hl q (fun _ => z) hsq heq W hW]
  exact B.fullGeometricSector_small_control hlarge _ _ V W hVW

end InitialCoverSystem
end AxisWindows

end SimpleAmenable
end
end

end OAI
