import OAI.CategoryTheory.Globular.CylinderLifting

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] {D B : GlobularFrame K}

structure CriticalData (e : Hom D B) (n : ℕ) (ε : Bool) where
  low : ∀ j, j < n → IsIso (e.obj j)
  iso : B.obj n ≅ D.obj (n+1)
  endpoint : e.obj n ≫ iso.hom = if ε then D.diagram.target n else D.diagram.source n

namespace CriticalData
variable {e : Hom D B} {n : ℕ} {ε : Bool} (c : CriticalData e n ε)
variable {S : GlobularSet.{v}} {Y : K}

noncomputable def stageOfFac (f : GlobularSet.Hom S (D.homGlob Y))
    (a : ∀ j, j ≤ n → S.Cell j → (B.obj j ⟶ Y))
    (ha : ∀ j hj x, e.obj j ≫ a j hj x = f.app j x) :
    GlobularSet.LiftStage (e.pre Y) f n where
  app := a
  fac := ha
  source_app j hj x := by
    let : IsIso (e.obj j) := c.low j (by omega)
    apply (cancel_epi (e.obj j)).1
    change e.obj j ≫ a j _ (S.source j x) = e.obj j ≫ B.diagram.source j ≫ a (j+1) hj x
    erw [ha, ← Category.assoc, ← e.source_naturality, Category.assoc, ha]
    exact f.source_app j x
  target_app j hj x := by
    let : IsIso (e.obj j) := c.low j (by omega)
    apply (cancel_epi (e.obj j)).1
    change e.obj j ≫ a j _ (S.target j x) = e.obj j ≫ B.diagram.target j ≫ a (j+1) hj x
    erw [ha, ← Category.assoc, ← e.target_naturality, Category.assoc, ha]
    exact f.target_app j x

noncomputable def initialCell
    (a : GlobularSet.Hom (S.whisker n ε) (D.homGlob Y))
    (j : ℕ) (hj : j ≤ n) (x : S.Cell j) : B.obj j ⟶ Y := by
  by_cases h : j < n
  · let : IsIso (e.obj j) := c.low j h
    exact inv (e.obj j) ≫ a.app j (.base j x)
  · have h' : j = n := by omega
    subst j
    exact c.iso.hom ≫ a.app (n+1) (.edge x)

theorem initialCell_low (a : GlobularSet.Hom (S.whisker n ε) (D.homGlob Y))
    (j : ℕ) (hj : j < n) (x : S.Cell j) :
    e.obj j ≫ c.initialCell a j (by omega) x = a.app j (.base j x) := by
  let : IsIso (e.obj j) := c.low j hj
  simp only [initialCell, dite_eq_left hj]
  erw [IsIso.hom_inv_id_assoc]

theorem initialCell_top (a : GlobularSet.Hom (S.whisker n ε) (D.homGlob Y))
    (x : S.Cell n) : c.initialCell a n le_rfl x = c.iso.hom ≫ a.app (n+1) (.edge x) := by
  simp only [initialCell, dite_eq_right (Nat.lt_irrefl n)]

theorem initialCell_fac (a : GlobularSet.Hom (S.whisker n ε) (D.homGlob Y))
    (j : ℕ) (hj : j ≤ n) (x : S.Cell j) :
    e.obj j ≫ c.initialCell a j hj x = a.app j (.base j x) := by
  by_cases h : j < n
  · exact c.initialCell_low a j h x
  · have hj' : j = n := by omega
    subst j
    erw [c.initialCell_top, ← Category.assoc, c.endpoint]
    cases ε with
    | false => exact (a.source_app n (.edge x)).symm
    | true => exact (a.target_app n (.edge x)).symm

noncomputable def initialStage (a : GlobularSet.Hom (S.whisker n ε) (D.homGlob Y)) :
    GlobularSet.LiftStage (e.pre Y) ((S.whiskerInclusion n ε).comp a) n :=
  c.stageOfFac _ (c.initialCell a) (c.initialCell_fac a)

end CriticalData

structure RelativeStage (e : Hom D B) {X Y : K} (p : X ⟶ Y)
    {S : GlobularSet.{v}} (f : GlobularSet.Hom S (D.homGlob X)) {m : ℕ}
    (b : GlobularSet.LiftStage (e.pre Y) (f.comp (post p)) m) (k : ℕ) (hk : k ≤ m) where
  stage : GlobularSet.LiftStage (e.pre X) f k
  fac_right : ∀ j (hj : j ≤ k) x, stage.app j hj x ≫ p = b.app j (hj.trans hk) x

namespace RelativeStage
variable [HasPushouts K] {e : Hom D B} {X Y : K} {p : X ⟶ Y}
variable {S : GlobularSet.{v}} {f : GlobularSet.Hom S (D.homGlob X)} {m k : ℕ}
variable {b : GlobularSet.LiftStage (e.pre Y) (f.comp (post p)) m} {hk : k ≤ m}

noncomputable def succ (a : RelativeStage e p f b k hk) (hk' : k+1 ≤ m)
    (hp : HasLiftingProperty (oneSidedMap e (k+1)) p) : RelativeStage e p f b (k+1) hk' := by
  let g := e.relativeMap p
  have H := e.relativeMap_liftsBoundary p (k+1) hp
  let z (x : S.Cell (k+1)) : (e.relativeGlob p).Cell (k+1) :=
    ⟨(b.app (k+1) hk' x, f.app (k+1) x), b.fac (k+1) hk' x⟩
  have hz (x : S.Cell (k+1)) :
      g.boundaryMap (k+1) (a.stage.nextBoundary x) = (e.relativeGlob p).boundary (k+1) (z x) := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact (a.fac_right k le_rfl (S.source k x)).trans (b.source_app k hk' x)
      · exact (a.stage.fac k le_rfl (S.source k x)).trans (f.source_app k x)
    · apply Subtype.ext
      apply Prod.ext
      · exact (a.fac_right k le_rfl (S.target k x)).trans (b.target_app k hk' x)
      · exact (a.stage.fac k le_rfl (S.target k x)).trans (f.target_app k x)
  choose l hlb hlg using fun x => H (a.stage.nextBoundary x) (z x) (hz x).symm
  let s := a.stage.extendTop l
    (fun x => congrArg (fun t => t.1.1) (hlb x))
    (fun x => congrArg (fun t => t.1.2) (hlb x))
    (fun x => congrArg (fun t => t.1.2) (hlg x))
  refine ⟨s, ?_⟩
  intro j hj x
  by_cases h : j ≤ k
  · simpa only [s, GlobularSet.LiftStage.extendTop, dite_eq_left h] using a.fac_right j h x
  · have hj' : j = k+1 := by omega
    subst j
    have hx : l x ≫ p = b.app (k+1) hk' x := congrArg (fun t => t.1.1) (hlg x)
    simpa only [s, GlobularSet.LiftStage.extendTop, dite_eq_right (by omega : ¬ k+1 ≤ k)] using hx

theorem succ_old (a : RelativeStage e p f b k hk) (hk' : k+1 ≤ m)
    (hp : HasLiftingProperty (oneSidedMap e (k+1)) p) (j : ℕ) (hj : j ≤ k) (x : S.Cell j) :
    (a.succ hk' hp).stage.app j (by omega) x = a.stage.app j hj x := by
  simp only [succ, GlobularSet.LiftStage.extendTop, dite_eq_left hj]

noncomputable def extendBy (a : RelativeStage e p f b k hk) :
    (d : ℕ) → (hd : k+d ≤ m) →
      (∀ j, k < j → j ≤ k+d → HasLiftingProperty (oneSidedMap e j) p) →
        RelativeStage e p f b (k+d) hd
  | 0, _, _ => a
  | d+1, hd, hp => (a.extendBy d (by omega) (fun j hj hj' => hp j hj (by omega))).succ hd
      (hp (k+d+1) (by omega) le_rfl)

theorem extendBy_old (a : RelativeStage e p f b k hk) (d : ℕ) (hd : k+d ≤ m)
    (hp : ∀ j, k < j → j ≤ k+d → HasLiftingProperty (oneSidedMap e j) p)
    (j : ℕ) (hj : j ≤ k) (x : S.Cell j) :
    (a.extendBy d hd hp).stage.app j (by omega) x = a.stage.app j hj x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [extendBy, succ_old _ _ _ j (hj.trans (Nat.le_add_right k d))]
    exact ih _ _

end RelativeStage

end GlobularFrame
end Grothendieck

end OAI
