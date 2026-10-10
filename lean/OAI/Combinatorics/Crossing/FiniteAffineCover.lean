import OAI.Combinatorics.Crossing.AffinePathHalves
import OAI.Combinatorics.Crossing.PolygonalChains
import OAI.Combinatorics.Crossing.PlanarSegments
import Mathlib.Data.Finset.Image

namespace OAI

noncomputable section
namespace Zarankiewicz

def HasFiniteAffineCover {a b : Plane} (γ : Path a b) : Prop :=
  ∃ S : Finset (unitInterval × unitInterval),
    (∀ ab ∈ S, ab.1 < ab.2) ∧
    (∀ t : unitInterval, ∃ ab ∈ S, ab.1 ≤ t ∧ t ≤ ab.2) ∧
    (∀ ab ∈ S, ∀ t : unitInterval,
      γ (intervalSegment ab.1 ab.2 t)=segmentPoint (γ ab.1) (γ ab.2) t.val)

theorem hasFiniteAffineCover_refl (a : Plane) : HasFiniteAffineCover (Path.refl a) := by
  classical
  refine ⟨{(0,1)},?_,?_,?_⟩
  · intro ab hab
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    norm_num
  · intro t
    exact ⟨(0,1),Finset.mem_singleton_self _,t.property.1,t.property.2⟩
  · intro ab hab t
    change a=segmentPoint a a t.val
    simp [segmentPoint,← add_smul]

theorem hasFiniteAffineCover_segment (a b : Plane) : HasFiniteAffineCover (Path.segment a b) := by
  classical
  refine ⟨{(0,1)},?_,?_,?_⟩
  · intro ab hab
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    norm_num
  · intro t
    exact ⟨(0,1),Finset.mem_singleton_self _,t.property.1,t.property.2⟩
  · intro ab hab t
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    simp only [intervalSegment_zero_one,Path.source,Path.target]
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]

theorem HasFiniteAffineCover.trans {a b c : Plane} {γ : Path a b} {η : Path b c}
    (hγ : HasFiniteAffineCover γ) (hη : HasFiniteAffineCover η) : HasFiniteAffineCover (γ.trans η) := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  obtain ⟨T,hTlt,hTcov,hTaff⟩ := hη
  let L : unitInterval × unitInterval → unitInterval × unitInterval := fun ab => (intervalLeft ab.1,intervalLeft ab.2)
  let R : unitInterval × unitInterval → unitInterval × unitInterval := fun ab => (intervalRight ab.1,intervalRight ab.2)
  refine ⟨S.image L ∪ T.image R,?_,?_,?_⟩
  · intro ab hab
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalLeft_strictMono (hSlt cd hcd)
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalRight_strictMono (hTlt cd hcd)
  · intro t
    by_cases ht : t.val ≤ 1/2
    · let u : unitInterval := ⟨2*t.val,by constructor <;> linarith [t.property.1]⟩
      obtain ⟨ab,hab,ha,hb⟩ := hScov u
      have hu : intervalLeft u=t := by apply Subtype.ext; change (2*t.val)/2=t.val; ring
      refine ⟨L ab,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩),?_,?_⟩
      · change intervalLeft ab.1 ≤ t
        rw [← hu]
        exact intervalLeft_strictMono.monotone ha
      · change t ≤ intervalLeft ab.2
        rw [← hu]
        exact intervalLeft_strictMono.monotone hb
    · let u : unitInterval := ⟨2*t.val-1,by constructor <;> linarith [t.property.2]⟩
      obtain ⟨ab,hab,ha,hb⟩ := hTcov u
      have hu : intervalRight u=t := by apply Subtype.ext; change (1+(2*t.val-1))/2=t.val; ring
      refine ⟨R ab,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩),?_,?_⟩
      · change intervalRight ab.1 ≤ t
        rw [← hu]
        exact intervalRight_strictMono.monotone ha
      · change t ≤ intervalRight ab.2
        rw [← hu]
        exact intervalRight_strictMono.monotone hb
  · intro ab hab t
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      change (γ.trans η) (intervalSegment (intervalLeft cd.1) (intervalLeft cd.2) t)=_
      rw [intervalSegment_left,path_trans_intervalLeft]
      exact (hSaff cd hcd t).trans (by simp only [L,path_trans_intervalLeft])
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      change (γ.trans η) (intervalSegment (intervalRight cd.1) (intervalRight cd.2) t)=_
      rw [intervalSegment_right,path_trans_intervalRight]
      exact (hTaff cd hcd t).trans (by simp only [R,path_trans_intervalRight])

theorem HasFiniteAffineCover.cast {a b c d : Plane} {γ : Path a b}
    (hγ : HasFiniteAffineCover γ) (ha : c=a) (hb : d=b) : HasFiniteAffineCover (γ.cast ha hb) := hγ

theorem polygonalArcPath_hasFiniteAffineCover (v : ℕ → Plane) :
    (k : ℕ) → HasFiniteAffineCover (polygonalArcPath v k)
  | 0 => hasFiniteAffineCover_refl _
  | 1 => hasFiniteAffineCover_segment _ _
  | k+2 => (polygonalArcPath_hasFiniteAffineCover v (k+1)).trans (hasFiniteAffineCover_segment _ _)

theorem PolygonalChain.hasFiniteAffineCover {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) : HasFiniteAffineCover P.path :=
  (polygonalArcPath_hasFiniteAffineCover P.vertices P.pieces).cast P.first.symm P.last.symm

end Zarankiewicz

end

end OAI
