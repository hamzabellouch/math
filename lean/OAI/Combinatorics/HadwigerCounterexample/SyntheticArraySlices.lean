import OAI.Combinatorics.HadwigerCounterexample.SyntheticParity
import OAI.Combinatorics.HadwigerCounterexample.RankSubrectangles

namespace OAI

/-! # Synthetic Array Slices -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module Function LinearMap
open scoped BigOperators
variable {p : Shape} {d e n N : ℕ}
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def exhibit (p : Shape) (A : Mat I J) (x : Display p I N) : Display p J N :=
  fun i => ((x i).1*A,(x i).2*A)

theorem exhibit_law (p : Shape) (A : Mat I J) (G : Mat I I)
    (h : Injective A.mulVec) (hn : 2*num I-(N:ℝ) ≤ -1) :
    mapW (displayLaw p I N G) (exhibit p A)=displayLaw p J N (pullM A A G) := by
  classical
  let C := fun x:Mat I I=> x=G
  have he : gramGood (U:=Fin N) G = FramesAt C := rfl
  have hl : 2*num I<num (Fin N) := by simp only [num,Fintype.card_fin] at *; linarith only [hn]
  have hh : ∃ x : Rack I N,FramesAt C x := framesAt_exists (show ∃ x, C x from ⟨_,rfl⟩)
    (by rw [←two_mul]; exact hl)
  have hv :
      mapW (unifOn (gramGood (U:=Fin N) G)) (observe A A) = unifOn (gramGood (pullM A A G)) :=
    framesAt_observe hh _ _ h h (fun i (hi : i=G)=>hi ▸ rfl)
  have ht:=mapW_repeat (fun _ : Comp p.g=> unifOn (gramGood G)) (fun _ => observe (U:=Fin N) A A)
  rw [hv] at ht; exact ht

omit [DecidableEq I] [DecidableEq J] in
theorem exhibit_color (p : Shape) (A : Mat I J) (u : Vec J) (x : Display p I N) (l : Tag p.g) :
    libColor p l u (exhibit p A x)=libColor p l (A *ᵥ u) x := by
  funext i j; cases j
  · exact (Matrix.mulVec_mulVec ..).symm
  exact (Matrix.mulVec_mulVec ..).symm

abbrev Sextant (d e : ℕ) := (Fin d ↪ Fin e) × (Fin d↪Fin e)
def reflectSextant (f : Sextant d e) : Hue d ↪ Hue e where
  toFun x := x.map (fun i=> (i.1,(onSide f i.1) i.2))
  inj' := by
    rintro (_|⟨a,b⟩) (_|⟨c,d⟩) h
    · rfl
    · cases h
    · cases h
    have he : (a,(onSide f a) b)=(c,(onSide f c) d) := Option.some.inj h
    have hh : a=c := congrArg Prod.fst he
    subst c; rw [(onSide f a).injective (congrArg Prod.snd he)]
def cartM (f : Sextant d e) := embedMat (reflectSextant f)

theorem cart_target (f : Sextant d e) :
    pullM (cartM f) (cartM f) (beamMap e) =
      (beamMap e).submatrix (reflectSextant f) (reflectSextant f) := by
  rw [cartM,pullM_def,embedMat_mul,mul_embedMat]; rfl

theorem cart_cross (p : Shape) (f : Sextant d e) (l : Tag p.g) (s : Augur p N)
    (x : Display p (Hue e) N) :
    let Z:= arches (libAug p l s (beamMap e) x)
    arches (libAug p l s (pullM (cartM f) (cartM f) (beamMap e)) (exhibit p (cartM f) x))
      = Z.submatrix f.1 f.2 := by
  classical
  intro Z
  let A:= cartM f
  have hu (i : Hue d) : A*ᵥjet i=jet (reflectSextant f i) := by
    funext j; simp only [jet,Matrix.mulVec_single_one,col_apply,A,cartM,embedMat,
      Matrix.of_apply]
    by_cases h : j= reflectSextant f i <;> simp [h]
  have hx (u : Vec (Hue d)) :
      libAug p l s (pullM A A (beamMap e)) (exhibit p A x) u =
      libAug p l s (beamMap e) x (A*ᵥu) := by unfold libAug libPredict; rw [evmat_pull,exhibit_color]
  ext i j
  change arches (libAug p l s (pullM A A (beamMap e)) (exhibit p A x)) i j=Z (f.1 i) (f.2 j)
  unfold arches Z; dsimp only
  simp_rw [hx,mulVec_add,hu]
  rfl

omit [Fintype I] [DecidableEq I] in
theorem col_flag {K : Type} [Fintype K] {M : Mat K I} {f : J → I}
    (h : Injective (M.submatrix _root_.id f).mulVec) : Injective f := by
  classical
  intro i j hi
  let X:=M.submatrix _root_.id f
  have he : jet i=jet j := h (by
    rw [jet,jet,mulVec_single_one,mulVec_single_one]
    funext k; simp only [col_apply,Matrix.submatrix_apply,hi])
  by_contra! hg
  have hf := congr_fun he i
  simp only [jet,Pi.single_eq_same,Pi.single_eq_of_ne hg] at hf
  exact one_ne_zero hf

set_option maxHeartbeats 600000 in
theorem rank_torpedo (M : Mat (Fin e) (Fin e)) (d : ℕ)
    (h : ∀ f : Sextant d e,(M.submatrix f.1 f.2).rank<d) :
    M.rank<d := by
  classical
  by_contra! hh
  obtain ⟨g,hg⟩ := basis_subcolumns M
  let a := g ∘ Fin.castLE hh
  let A := M.submatrix _root_.id a
  have ha :
      Injective A.mulVec := inject_column_slice (M.submatrix _root_.id g) hg (Fin.castLE_injective hh)
  have hk : Aᵀ.rank=d := (Matrix.rank_transpose _).trans
    ((mrk_inj.mp ha).trans (Fintype.card_fin _))
  obtain ⟨f,hf⟩ : ∃ f : Fin d→Fin e,Injective (Aᵀ.submatrix _root_.id f).mulVec := by
    have he := basis_subcolumns Aᵀ; rwa [hk] at he
  let B := M.submatrix f a
  have hz : B.rank=d := by
    rw [← Matrix.rank_transpose]
    exact (mrk_inj.mp hf).trans (Fintype.card_fin _)
  have h1 : Injective a := col_flag ha
  have h2 : Injective f := col_flag hf
  have hu := h ⟨⟨f,h2⟩,⟨a,h1⟩⟩
  exact (ne_of_lt hu) hz
end HadwigerCounterexample

end

end OAI
