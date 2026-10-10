import OAI.Combinatorics.HadwigerCounterexample.GroupedQueryIndependence

namespace OAI

/-! # Query Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Module Matrix Finset Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I G A K D : Type} [Fintype I] [Fintype G] [Fintype A]
variable [Fintype K] [Fintype D] [DecidableEq I] [DecidableEq G] [DecidableEq K]

structure Program (p : Shape) (n : ℕ) {I G : Type} (g : Route I G) (A : Type) where
  left : A→NomQuery p n g
  right : A→NomQuery p n g

variable {g : Route I G}

namespace Program
variable (s : Program p n g A)

def free (x : K→ A) :=
  (∀ i,Injective (pooled (s.left ∘ x) i).mulVec)∧
  (∀ i,Injective (pooled (s.right ∘ x) i).mulVec)

def showKey (x : A) (o : Forum p n N G) :=
  peekR p g (s.left x) (s.right x) o

def oexpect (w : Wgt A) (F : A → Rack I N → ℝ) (o : Forum p n N G) :=
  avg w (fun x => F x (s.showKey x o))
end Program

theorem forum_law (m : Mixer p n) {N : ℕ} (hN : 2*num (Full p n)<N) :
    IsLaw (forumLaw m N (G:=G)) :=
  prodW_law (fun _ => unifOn_law (framesAt_exists (gramCond_exists m)
    (by rw [←two_mul]; simpa only [num,Fintype.card_fin] using hN)))

theorem avg_bound1 {w : Wgt A} (hw : IsLaw w) (f : Wgt A) (hf : ∀ x,|f x|≤1) :
    |avg w f|≤1 := (abs_avg_le hw.nz).trans (hw.avg_le hf)
theorem avg_cross_sq (w : Wgt A) (f : Wgt A) :
    avg w f ^ 2=avg (draws Bool w) (fun q => f (q true)* f (q false)) := by
  let g (i : Bool) := f
  have hh := prodW_avg (fun _ : Bool => w) g
  have he : prodW g=(fun q => f (q true)* f (q false)) := by ext; unfold prodW; rw [Fintype.prod_bool]
  rw [he,Fintype.prod_bool] at hh; rw [pow_two]; exact hh.symm

theorem avg_var (w : Wgt A) (f : Wgt A) (hw : IsLaw w) :
    avg w (fun x => (f x-avg w f)^2) = avg w (fun x => f x^2) - (avg w f)^2 := by
  let g := avg w f
  have hh (x) : (f x-g)^2=f x^2-2*g*f x+g^2 := by ring
  change avg w (fun x => (f x-g)^2)=_
  simp_rw [hh,avg_add,avg_sub,avg_mul',hw.avg_const]
  unfold g; ring

namespace Program
variable {s : Program p n g A}

set_option maxHeartbeats 800000 in
theorem oVar (m : Mixer p n) (hN : 2*num (Full p n) < N)
    (T : A→Wgt (Rack I N))
    (w : Wgt A) (hw : IsLaw w) (hT : ∀ i x,|T i x|≤1)
    (k : ℝ) (hk : ∀ i,num (Port (tied g Bool) i)≤k)
    (hK : 2*k-N≤-1)
    (r : ℝ) (hr : pr (draws Bool w) (fun x => ¬ s.free x) ≤ r) :
    let v := forumLaw (G:=G) m N
    let f := s.oexpect w T
    avg v (fun o => (f o-avg v f)^2) ≤
      2*r + 2*netFact (tied g Bool)*twinkle (tied g Bool) k N := by
  classical
  let v := forumLaw (G:=G) m N
  let f := s.oexpect w T
  let F (x : A) := fun o => T x (s.showKey x o)
  let D := draws Bool w
  let B := 2*netFact (tied g Bool)*twinkle (tied g Bool) k N
  have hD : IsLaw D := draws_law hw
  have hv : IsLaw v := forum_law _ hN
  let V (x : Bool→A) := avg v (fun o => F (x true) o * F (x false) o)
  let W (x : Bool→A) := avg v (F (x true))*avg v (F (x false))
  have hW :
      (avg v f)^2 = avg D W := by
    unfold f oexpect
    rw [avg_avg,avg_cross_sq]
  have hV :
      avg v (fun x => f x^2) = avg D V := by
    unfold f oexpect; simp_rw [avg_cross_sq]; rw [avg_avg]
  have hi x :
      V x-W x ≤ 2*ind (¬s.free x)+B := by
    by_cases he : s.free x
    · have hh := pooled_batch (s.left ∘ x) (s.right ∘ x) m hN k hk hK he.1 he.2
        (T ∘ x) (fun i y => hT _ _)
      simp_rw [Fintype.prod_bool] at hh
      rw [ind_zero (fun h => h he),mul_zero,zero_add]
      exact (le_abs_self _).trans hh
    have h1 (a b : ℝ) (h : |a|≤1) (g : |b|≤1) : |a*b|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul h g (abs_nonneg _) zero_le_one).trans_eq (by ring)
    have hh : |W x|≤1 := h1 _ _ (avg_bound1 hv _ (fun y => hT _ _)) (avg_bound1 hv _
      (fun y => hT _ _))
    have hg : |V x|≤1 := avg_bound1 hv _ (fun i => h1 _ _ (hT _ _) (hT _ _))
    have ht : 0 ≤ twinkle (tied g Bool) k N := add_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (bp_pos _).le)) (bp_pos _).le
    have h2 : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) netFact_pos.le) ht
    rw [ind_one he,mul_one]
    exact sub_le_iff_le_add.mpr (by linarith [(abs_le.mp hh).1,(abs_le.mp hg).2])
  change avg v _ ≤ _
  rw [avg_var v f hv,hW,hV,← avg_sub]
  apply (avg_mono hD.nz hi).trans
  rw [avg_add,avg_mul',hD.avg_const]
  exact add_le_add_left (mul_le_mul_of_nonneg_left hr (by norm_num)) _

def oFreq (w : Wgt A) (F : A → Rack I N→Prop) (o : Forum p n N G)
    (s : Program p n g A) :=
  pr w (fun i => F i (s.showKey i o))

set_option maxHeartbeats 800000 in
theorem oTail (m : Mixer p n) (hN : 2*num (Full p n) < N)
    (T : A→Rack I N →Prop)
    (w : Wgt A) (hw : IsLaw w)
    {k : ℝ} {l : ℕ} (hk : ∀ i,num (Port (tied g (Fin l)) i)≤k)
    (hK : 2*k-N≤-1)
    (r : ℝ) (hr : pr (draws (Fin l) w) (fun x => ¬ s.free x) ≤ r)
    {ε : ℝ} (hε : 0 ≤ ε) :
    let v := forumLaw (G:=G) m N
    let f := (fun o => oFreq w T o s)
    (ε^l - r)*pr v (fun x => ε ≤ f x) ≤ netFact (tied g (Fin l))* (avg v f)^l := by
  classical
  let v := forumLaw (G:=G) m N
  let f := (fun o : Forum p n N G => oFreq w T o s)
  have hv : IsLaw v := forum_law _ hN
  let F := draws (Fin l) w
  have hF : IsLaw F := draws_law hw
  let P (x) (y : Fin l→A) := ∀ i,T (y i) (s.showKey (y i) x)
  have hh (x) : pr F (fun y => P x y)= f x ^ l := by
    unfold P F draws
    rw [prodW_pr (fun (_ : Fin l) => w) (fun _ i => T i (s.showKey i x))]
    simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin]
    rfl
  let Q (x : Fin l → A) := s.free x
  let S (o) (x : Fin l→A) := P o x ∧ Q x
  have hi (o) :
      (ε^l-r)*ind (ε≤f o)≤ pr F (S o) := by
    by_cases ht : ε≤f o
    · rw [ind_one ht,mul_one]
      refine (sub_le_sub (pow_le_pow_left₀ hε ht l) hr).trans ?_
      rw [←hh]; exact pr_shield hF.nz _ _
    rw [ind_zero ht,mul_zero]; exact pr_nonneg hF.nz
  let W (x) := pr v (fun i => T x (s.showKey x i))
  let C := netFact (tied g (Fin l))
  have hq (x : Fin l → A) :
      pr v (fun i => S i x) ≤ C*∏ i:Fin l,W (x i) := by
    by_cases he : Q x
    · have hg := pool_upper (s.left ∘ x) (s.right ∘ x) m hN he.1 he.2
        (fun i => by linarith only [hk i,hK]) (T ∘ x)
      simp only [S,he,and_true]
      exact hg
    simp only [S,he,and_false,pr_false]; exact mul_nonneg netFact_pos.le
      (Finset.prod_nonneg fun i _ => pr_nonneg hv.nz)
  have hg : avg v f=avg w W := avg_avg _ _ _
  have he := avg_mono hv.nz hi
  rw [avg_mul'] at he
  change _ ≤ _
  apply le_trans he
  calc avg v (fun x => pr F (S x)) = avg F (fun y => pr v (fun x => S x y)) := avg_avg _ _ _
       _ ≤ avg F (fun x => C*∏ i,W (x i)) := avg_mono hF.nz hq
       _ = netFact _ * (avg v f)^l := by rw [avg_mul',hg, poweravg]
end Program
end HadwigerCounterexample

end

end OAI
