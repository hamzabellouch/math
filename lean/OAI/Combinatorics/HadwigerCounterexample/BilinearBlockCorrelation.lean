import OAI.Combinatorics.HadwigerCounterexample.OppositeEndpointForms

namespace OAI

/-! # Bilinear Block Correlation -/

noncomputable section
namespace HadwigerCounterexample
open Finset LinearMap Module Matrix Function
open scoped BigOperators
variable {p : Shape} {I J A : Type} [Fintype I] [Fintype J] [Fintype A]
variable {n : ℕ}

def spring (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (y : Knobs p.g n) := point p s (lit f l y)

theorem spring_update (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (y : Knobs p.g n) (B) (h : f.keeps l B) (z : Vec (Fin n)) :
    spring p l s f (update y B z)= spring p l s f (update y B 0)+
      blockRay p n s B *ᵥ z := by
  classical
  have he : baseV (lit f l (update y B z))=baseV (lit f l (update y B 0))+blockA p n B *ᵥ z := by
    funext a
    rcases a with _|⟨d,j⟩
    · simp [baseV,blockA,mulVec,dotProduct,embedMat]
    by_cases hk : d=B
    · subst d; simp [baseV,blockA,mulVec,dotProduct,embedMat,lit,h]
    simp [baseV,blockA,mulVec,dotProduct,embedMat,lit,hk]
  unfold spring point blockRay
  rw [he,map_add,←Matrix.mulVec_mulVec,labMat_act]

private def dotLB (I : Type) [Fintype I] : Vec I →ₗ[F] Vec I→ₗ[F] F where
  toFun := dotL
  map_add' p q := LinearMap.ext fun i => add_dotProduct p q i
  map_smul' a p := LinearMap.ext fun i => by
    change dotProduct (a • p) i=a*dotProduct p i
    rw [smul_dotProduct]; rfl

theorem spark_walsh [DecidableEq I] [DecidableEq J] (M : Mat I J) (p : Wgt (Vec I)) (q : Wgt (Vec J))
    (hp : ∀ i, |p i|≤1) (hq : ∀ i, |q i|≤1) :
    |avg (pairW unif unif) (fun i => wsign (evmat M i.1 i.2)*(p i.1*q i.2))| ≤
      bp (-(M.rank:ℝ)/2) := by
  classical
  let Q := dotLB I
  let L := Q ∘ₗ M.mulVecLin
  have he (i j) : evmat M i j=L j i := dotProduct_comm ..
  have hh : Injective Q := fun x y h => funext (fun i => by
    have hg := LinearMap.congr_fun h (Pi.single i 1)
    change dotProduct x (Pi.single i 1)=dotProduct y (Pi.single i 1) at hg
    simpa using hg)
  have ht : rk L=M.rank := by
    have h : LinearMap.ker L=LinearMap.ker M.mulVecLin := by
      ext x; change Q (M.mulVecLin x)=0 ↔ M.mulVecLin x=0
      rw [← map_zero Q,hh.eq_iff]
    have hv := L.finrank_range_add_finrank_ker
    rw [h, ← M.mulVecLin.finrank_range_add_finrank_ker] at hv
    exact Nat.add_right_cancel hv
  rw [pairW_avg]
  have hz (x : Vec I) (y : Vec J) : wsign (evmat M x y)*(p x*q y)=p x*(q y*wsign (L y x)) := by
    rw [he]; ring
  simp_rw [hz,avg_mul']
  rw [←ht]
  exact walsh_bound _ q p hq hp

set_option maxHeartbeats 800000 in
theorem spark_uncap (p : Shape) (M : Moment p n) (s t : Label p.b) (l j : Tag p.g)
    (f g : Flavor p.g) (B) (hB : f.keeps l B) (hB' : g.keeps j B)
    (w u : Wgt (Knobs p.g n)) (hw : ∀ i,|w i| ≤ 1) (hu : ∀ i,|u i|≤1) :
    let Q i z := evmat M (spring p l s f i) (spring p j t g z)
    |avg (pairW unif unif) (fun x => wsign (Q x.1 x.2)*(w x.1*u x.2))|≤
      bp (-(blockRank B s t M:ℝ)/2) := by
  classical
  intro Q
  let F (x : Knobs p.g n × _) := wsign (Q x.1 x.2)*(w x.1*u x.2)
  let K := Wgt (Vec (Fin n))
  let v : Block p.g→ K := fun _ => unif
  have ht := update2_avg v v B F unif_law unif_law
  have he : prodW v=unif := draws_unif.symm
  let R := blockRay p n s B; let S:=blockRay p n t B
  let H := pullM R S M
  have hi (x y : Knobs p.g n) :
      |avg (pairW (v B) (v B)) (fun i => F (update x B i.1,update y B i.2))|≤
      bp (-(blockRank B s t M:ℝ)/2) := by
    let X := spring p l s f (update x B 0); let Y := spring p j t g (update y B 0)
    let A i := evmat M (R *ᵥ i) Y; let D j := evmat M X (S *ᵥ j)+evmat M X Y
    let Z i := wsign (A i)*w (update x B i); let W j := wsign (D j)*u (update y B j)
    have hp i j' :
        Q (update x B i) (update y B j')= evmat H i j'+(A i+D j') := by
      unfold Q; rw [spring_update _ _ _ _ _ _ hB,spring_update _ _ _ _ _ _ hB']
      unfold H A D X Y; rw [evmat_pull]
      simp only [evmat,mulVec_add,add_dotProduct,dotProduct_add,R,S]; ac_rfl
    have hh i j : F (update x B i,update y B j)=wsign (evmat H i j)*(Z i*W j) := by
      unfold F Z W; dsimp only; rw [hp,wsign_add,wsign_add]; ring
    have hz i : |Z i|≤1 := by unfold Z; rw [abs_mul,wsign_abs,one_mul]; exact hw _
    have hy i : |W i|≤1 := by unfold W; rw [abs_mul,wsign_abs,one_mul]; exact hu _
    simp_rw [hh]
    exact spark_walsh _ Z W hz hy
  simp only [he] at ht
  change |avg (pairW unif unif) F|≤_
  rw [ht]
  let hq := pairW_law (α:=Knobs p.g n) (β:=Knobs p.g n) unif_law unif_law
  exact (abs_avg_le hq.nz).trans (hq.avg_le fun x => hi x.1 x.2)
end HadwigerCounterexample

end

end OAI
