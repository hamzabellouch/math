import OAI.Combinatorics.HadwigerCounterexample.PolynomialRankBounds

namespace OAI

/-! # Four Phase Bits -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
abbrev Quad := Party × Party

def quench (p : Shape) {n N} (Δ : UnitType p n N→ Ambient p N)
    (x : UnitType p n N × UnitType p n N) : Quad :=
  (fun i => tone p x.2 (unary i) (Δ x.1),fun i => tone p x.1 (unary i) (Δ x.2))

def quadDot (x y : Quad) := dotProduct x.1 y.1 + dotProduct x.2 y.2
def quadPhase (x y : Quad) := wsign (quadDot x y)

private theorem party_card : Fintype.card Party = 4 := by simp [Party,Vec,F]
theorem quad_card : Fintype.card Quad=16 := by simp [Quad]
private theorem quad_rate (x : Quad) : unif x=(1:ℝ)/16 := by
  rw [unif_apply,quad_card]; norm_num

theorem quad_inv_zero (x : Quad) : avg unif (fun y => quadPhase y x)=ind (x=0) := by
  classical
  let B := (dotL x.1).coprod (dotL x.2)
  have h (y) : quadPhase y x=wsign (B y) := by
    change wsign (dotProduct y.1 x.1+dotProduct y.2 x.2)=wsign (dotProduct x.1 y.1+dotProduct x.2 y.2)
    rw [dotProduct_comm x.1,dotProduct_comm x.2]
  have he : B=0 ↔ x=0 := by
    constructor
    · intro he
      have hl : dotL x.1=0 := LinearMap.ext fun z => by
        have hf : dotL x.1 z+dotL x.2 0=0 := LinearMap.congr_fun he (z,0)
        rwa [map_zero,add_zero] at hf
      have hr : dotL x.2=0 := LinearMap.ext fun z => by
        have hf : dotL x.1 0+dotL x.2 z=0 := LinearMap.congr_fun he (0,z)
        rwa [map_zero,zero_add] at hf
      refine Prod.ext (dot_ext_zero (fun y => ?_)) (dot_ext_zero (fun y => ?_))
      · rw [dotProduct_comm]; exact LinearMap.congr_fun hl y
      rw [dotProduct_comm]; exact LinearMap.congr_fun hr y
    · intro he
      refine LinearMap.ext fun y => ?_
      unfold B; rw [he]
      change dotProduct (0:Party) y.1 +dotProduct (0:Party) y.2=0
      rw [zero_dotProduct,zero_dotProduct]; simp
  simp_rw [h,wsign_lin,he]

theorem quad_inv (x y : Quad) : ind (x=y)=avg unif (fun S => quadPhase S x*quadPhase S y) := by
  classical
  have he (S) : quadPhase S (x+y) = quadPhase S x*quadPhase S y := by
    unfold quadPhase quadDot
    rw [← wsign_add]
    simp only [Prod.fst_add,Prod.snd_add,dotProduct_add,add_comm,add_left_comm]
  simp_rw [← he,quad_inv_zero]
  apply congrArg ind
  exact propext (by rw [← ZModModule.sub_eq_add,sub_eq_zero])
private theorem joint_phase (p : Shape) {n N} (Δ : UnitType p n N→ Ambient p N) (x) (S) :
    quadPhase S (quench p Δ x) = chant p Δ S.1 S.2 x := by
  unfold quadPhase chant
  unfold quadDot quench
  dsimp only
  rw [←tone_vec, ←tone_vec,add_comm]

theorem quad_invert (p : Shape) {n N} (Δ : UnitType p n N→Ambient p N) (w) (s : Quad) :
    pr (pairW w w) (fun x => quench p Δ x=s)=
    avg unif (fun v : Quad => pitch p Δ w v.1 v.2 * quadPhase v s) := by
  unfold pr
  simp_rw [quad_inv, joint_phase]
  rw [avg_avg]
  simp_rw [avg_mul]
  rfl

theorem mix_pattern (p : Shape) {n N} (Δ : UnitType p n N→Ambient p N) (w)
    (hw : IsLaw w) (h : tonalMix p Δ w) (s : Quad) :
    0.05 < pr (pairW w w) (fun x => quench p Δ x=s) := by
  classical
  rw [quad_invert]
  let f := fun S : Quad => ind (S=0) - 0.005
  have hf S : f S≤pitch p Δ w S.1 S.2*quadPhase S s := by
    by_cases hS : S=0
    · have h0 : pitch p Δ w 0 0=1 := by
        unfold pitch
        have hz (x : UnitType p n N) y : tone p x 0 (Δ y)=0 := by rw [tone_vec,zero_dotProduct]
        simp_rw [hz,add_zero, wsign_zero]; exact (pairW_law hw hw).avg_const _
      rw [hS]
      change f 0≤pitch p Δ w 0 0*quadPhase 0 s
      rw [h0]
      norm_num [f,quadPhase,quadDot]
    · have hh := h _ _ (show S.1≠0 ∨ S.2≠0 from by
        by_contra! he; exact hS (Prod.ext he.1 he.2))
      have he : |pitch p Δ w S.1 S.2*quadPhase S s| < 0.005 := by rwa [abs_mul,quadPhase,wsign_abs,mul_one]
      simpa only [f,ind_zero hS,zero_sub] using (abs_lt.mp he).1.le
  apply lt_of_lt_of_le _ (avg_mono unif_law.nz hf)
  unfold f; rw [avg_sub, unif_law.avg_const]
  change 0.05 < pr unif (fun S : Quad => S=0)-0.005
  rw [pr_point',quad_rate]; norm_num

/-- common even relation on four scores. -/
def repeated (x : Quad) :=
  dotProduct allSide x.1=0 ∧ dotProduct allSide x.2=0

def repeatQ (i : F) : Quad := (fun _ => i,fun _ => i)

def evenP : Finset Party := {0,allSide}
def evenQ : Finset Quad := evenP×ˢevenP

private theorem party_single (x : Party) (h : x∉evenP) : ∃ i,x=unary i := by
  classical
  rcases bit_cases (x true) with a|a <;> rcases bit_cases (x false) with b|b
  · have he : x=0 := funext fun i => by cases i; exact b; exact a
    simp [he,evenP] at h
  · refine ⟨false,funext fun i => ?_⟩; cases i <;> simp [a,b,unary]
  · refine ⟨true,funext fun i => ?_⟩; cases i <;> simp [a,b,unary]
  have he : x=allSide := funext fun i => by cases i; exact b; exact a
  simp [he,evenP] at h

private theorem even_dot (_ : Quad) (v : Quad) (h : v∈evenQ) (j : F) :
    quadPhase v (repeatQ j)=1 := by
  classical
  have he (b : Party) (h : b∈evenP) : dotProduct b (fun _ => j)=0 := by
    have h : b=0 ∨ b=allSide := by simpa [evenP] using h
    rcases h with h|h
    · rw [h,zero_dotProduct]
    simp only [h,dotProduct,Fintype.sum_bool,allSide,one_mul,char_two]
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp h
  unfold quadPhase quadDot repeatQ
  dsimp only
  rw [he _ ha,he _ hb]; simp

private theorem even_sum (x : Quad) (i : F) :
    ∑ v∈evenQ,quadPhase v x*quadPhase v (repeatQ i)=4*ind (repeated x) := by
  classical
  let f (x : Party) (v : Party) := wsign (dotProduct v x)
  have hh (x) :
      ∑ v∈evenP,f x v=2*ind (dotProduct allSide x=0) := by
    have hn : allSide≠0 := by
      intro e
      have hh := congr_fun e true
      change (1:F)=0 at hh; simp at hh
    simp only [evenP,Finset.sum_insert (show (0:Party)∉ ({allSide}:Finset _) from
      fun h => hn (mem_singleton.mp h).symm),Finset.sum_singleton,f, zero_dotProduct, wsign_zero]
    by_cases ht : dotProduct allSide x=0
    · norm_num [ind,ht]
    norm_num [ind,ht,wsign]
  have ht (v : Quad) (h : v∈evenQ) : quadPhase v x * quadPhase v (repeatQ i)
      = f x.1 v.1 * f x.2 v.2 := by
    rw [even_dot x _ h,mul_one,quadPhase,quadDot,wsign_add]
  rw [Finset.sum_congr (g:=fun v => f x.1 v.1 * f x.2 v.2) rfl ht,evenQ, Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,hh,hh,repeated,ind_and]; ring

set_option maxHeartbeats 800000 in
theorem tiny_pattern (p : Shape) {n N} (Δ : UnitType p n N→Ambient p N) (w)
    (i : F) {h : ℝ} (h0 : 0≤h)
    (hw : ∀ i : Bool,∀ R, |pitch p Δ w (unary i) R|≤h) :
    (1/4:ℝ)*pr (pairW w w) (fun x => repeated (quench p Δ x))-h ≤
      pr (pairW w w) (fun x => quench p Δ x=repeatQ i) := by
  classical
  let f (v : Quad) := pitch p Δ w v.1 v.2*quadPhase v (repeatQ i)
  let μ := pairW w w
  let g (S : Quad) := ind (S∈evenQ)*f S
  have he (x : Quad) : g x - h ≤ f x := by
    by_cases hx : x∈evenQ
    · unfold g; rw [ind_one hx,one_mul]
      exact sub_le_self _ h0
    have hi : |pitch p Δ w x.1 x.2|≤h := by
      by_cases he : x.1∈evenP
      · obtain ⟨i,hit⟩ := party_single x.2 (fun hh => hx (Finset.mem_product.mpr ⟨he,hh⟩))
        rw [hit,pitch_turn]
        exact hw i _
      obtain ⟨i,hi⟩ := party_single _ he
      rw [hi]; exact hw i _
    have hs : |f x|≤h := by unfold f quadPhase; rwa [abs_mul,wsign_abs,mul_one]
    unfold g; rw [ind_zero hx,zero_mul,zero_sub]
    exact (abs_le.mp hs).1
  have hg : avg unif g=(1/4:ℝ)*pr μ (fun x => repeated (quench p Δ x)) := by
    have ht : ∑ x : Quad,g x= ∑ x∈evenQ,f x := by
      symm
      simp only [g,ind,ite_mul,one_mul,zero_mul,← Finset.sum_filter]
      simp
    have hB (x : Quad) :
        f x=avg μ (fun y => quadPhase x (quench p Δ y)*quadPhase x (repeatQ i)) := by
      rw [avg_mul]; simp_rw [joint_phase]; rfl
    have hf : ∑ x∈evenQ,f x=4*pr μ (fun x => repeated (quench p Δ x)) := by
      simp_rw [hB,← avg_sum,even_sum,avg_mul']; rfl
    simp only [avg,quad_rate,← Finset.mul_sum, ht,hf]
    unfold pr avg
    ring
  rw [quad_invert,show _*pr _ _=_ from hg.symm]
  calc avg unif g - h = avg unif (fun x => g x-h) := by rw [avg_sub,unif_law.avg_const]
       _ ≤ _ := avg_mono unif_law.nz he

end HadwigerCounterexample

end

end OAI
