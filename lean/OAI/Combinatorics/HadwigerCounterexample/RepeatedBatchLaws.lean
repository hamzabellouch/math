import OAI.Combinatorics.HadwigerCounterexample.ConditionedBatchLaws

namespace OAI

/-! # Repeated Batch Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G] [DecidableEq I]
variable [DecidableEq J] [DecidableEq G] {p : Shape} {n N : ℕ}

def tied (f : Route I G) (J : Type) : Route (J×I) G := f ∘ Prod.snd
variable {f : Route I G}

def pooled (A : J → NomQuery p n f) : NomQuery p n (tied f J) :=
  fun g => Matrix.of (fun i j => A j.val.1 g i (⟨j.val.2,j.property⟩))

omit [Fintype I] [Fintype J] [Fintype G] [DecidableEq I] [DecidableEq J] [DecidableEq G] in
theorem peek_pooled (A B : J→NomQuery p n f) (x : Forum p n N G) (i : J) :
    led i (peekR p (tied f J) (pooled A) (pooled B) x)=peekR p f (A i) (B i) x := by
  apply Prod.ext <;> ext <;> rfl

omit [Fintype I] [Fintype J] [Fintype G] [DecidableEq I] [DecidableEq J] [DecidableEq G] in
theorem lane_pooled (A B : J→NomQuery p n f) (m : Mixer p n) (i : J) :
    laneM (database m (pooled A) (pooled B)) i=database m (A i) (B i) := by
  funext z; ext x y; rfl

omit [Fintype G] in
theorem pool_injective {A : J → NomQuery p n f} (h : ∀ i, Injective (pooled A i).mulVec) :
    ∀ z i,Injective (A z i).mulVec := by
  classical
  intro z i
  let e := condLane (tied f J) z i
  have he : Injective e := by
    intro a b h; exact Subtype.ext (congrArg (fun x : Port (tied f J) i => x.val.2) h)
  have ho : A z i=pooled A i*embedMat e := by rw [mul_embedMat]; rfl
  rw [ho]; exact inj_comp_mat _ _ (h i) (embedMat_inj he)

theorem poUse (A B : J→NomQuery p n f) (m : Mixer p n)
    (hN : 2*num (Full p n)<N)
    (ha : ∀ i,Injective (pooled A i).mulVec) (hb : ∀ i, Injective (pooled B i).mulVec)
    (F : Wgt (Rack (J×I) N)) :
    avg (forumLaw m N) (fun x => F (peekR p (tied f J) (pooled A) (pooled B) x))=
      avg (rackStation (database m (pooled A) (pooled B)) N) F := by
  rw [← mapW_avg,law_peekR m hN ha hb]

set_option maxHeartbeats 800000 in
theorem pooled_batch (A B : J → NomQuery p n f) (m : Mixer p n)
    (hN : 2*num (Full p n)<N)
    (k : ℝ) (hk : ∀ i,num (Port (tied f J) i)≤k)
    (hL : 2*k-N≤-1)
    (ha : ∀ i, Injective (pooled A i).mulVec)
    (hb : ∀ i, Injective (pooled B i).mulVec)
    (F : J→ Wgt (Rack I N)) (hf : ∀ i x,|F i x|≤1) :
    let w := forumLaw (G:=G) m N
    |avg w (fun x => ∏ i, F i (peekR p f (A i) (B i) x)) -
      ∏ i, avg w (fun x => F i (peekR p f (A i) (B i) x))|≤
      2*netFact (tied f J)*twinkle (tied f J) k N := by
  classical
  let w := forumLaw m N (G:=G)
  let Z := database m (pooled A) (pooled B)
  have he i :
      avg w (fun x => F i (peekR p f (A i) (B i) x))=
        avg (rackStation (database m (A i) (B i)) N) (F i) := by
    unfold w; rw [←mapW_avg,law_peekR m hN (pool_injective ha i) (pool_injective hb i)]
  have hx :
      avg w (fun x => ∏ i, F i (peekR p f (A i) (B i) x)) =
        avg (rackStation Z N) (brightProd F) := by
    rw [show avg (rackStation Z N) _ =_ from (poUse A B m hN ha hb (brightProd F)).symm]
    refine avg_congr fun x _ => ?_
    simp_rw [brightProd, peek_pooled]
  dsimp only
  change |avg w _ - ∏ i, avg w _| ≤ _
  simp_rw [he]; rw [hx]
  have hi := compare_lanes Z F hf k hk (fun i => by linarith only [hk i,hL])
  simp_rw [Z,lane_pooled] at *
  exact hi

set_option maxHeartbeats 600000 in
theorem pool_upper (A B : J → NomQuery p n f) (m : Mixer p n)
    (hN : 2*num (Full p n)<N)
    (ha : ∀ i, Injective (pooled A i).mulVec)
    (hb : ∀ i, Injective (pooled B i).mulVec)
    (hL : ∀ i,2*num (Port (tied f J) i)-N ≤ -1) (P : J→Rack I N → Prop) :
    let w := forumLaw (G:=G) m N
    pr w (fun x => ∀ i,P i (peekR p f (A i) (B i) x))≤
      netFact (tied f J)* ∏ i, pr w (fun x => P i (peekR p f (A i) (B i) x)) := by
  classical
  let w := forumLaw (G:=G) m N
  let S := database m (pooled A) (pooled B)
  let q (x : Rack (J×I) N) := ∀ i,P i (led i x)
  have h1 i :
      pr w (fun x => P i (peekR p f (A i) (B i) x)) =
        pr (rackStation (database m (A i) (B i)) N) (P i) := by
    unfold w; rw [←mapW_pr,law_peekR m hN (pool_injective ha i) (pool_injective hb i)]
  have ht :
      pr w (fun x => ∀ i,P i (peekR p f (A i) (B i) x)) =
        pr (rackStation S N) q := by
    rw [show pr (rackStation S N) q= _ from
      (poUse A B m hN ha hb (fun x => ind (q x))).symm]
    refine avg_congr fun x _ => ?_
    simp_rw [q,peek_pooled]
  let M := netFact (tied f J)
  let g (i : J) := bothPart (laneM S i) (N:=N)
  have hg x (hh : bothPart S x ∧ q x) :
      ∀ i,g i (led i x)∧ P i (led i x) := fun i => ⟨laneGram S _ hh.1 _,hh.2 i⟩
  change pr w _ ≤ _
  rw [ht, rackStation,← on_unif,pr_on]
  have hx : pr unif (fun x : Rack (J×I) N => ∀ i,g i (led i x)∧ P i (led i x)) =
      ∏ i,pr unif (fun x => g i x∧P i x) := by
    change avg unif _=_
    simp_rw [ind_all]
    exact led_piece Finset.univ (fun i x => g i x∧P i x)
  have hh0 := net_norm S N hL
  refine (div_le_div₀ (pr_nonneg unif_law.nz)
    (pr_mono unif_law.nz hg) (inv_pos_of_pos netFact_pos) hh0.1).trans ?_
  rw [hx,div_eq_mul_inv,inv_inv,mul_comm]
  apply mul_le_mul_of_nonneg_left _ netFact_pos.le
  refine Finset.prod_le_prod₀ (fun i _ => pr_nonneg unif_law.nz) (fun i _ => ?_)
  rw [pr_of_on unif_law.nz (g _),on_unif,h1]
  have h0 (i) : pr unif (g i)≤1 := (pr_le_tot unif_law.nz).trans unif_law.total.le
  apply le_trans (mul_le_mul_of_nonneg_right (h0 _) (pr_nonneg (unifOn_sub _).nz))
  unfold g S; rw [lane_pooled,one_mul]; exact le_rfl

end HadwigerCounterexample

end

end OAI
