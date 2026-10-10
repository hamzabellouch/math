import OAI.Combinatorics.HadwigerCounterexample.PredictedDualCoefficients

namespace OAI

/-! # Predicted Dual Evaluation -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset Function LinearMap Module
open scoped BigOperators
namespace StatusAnalysis
namespace DualAnalysis
open PredictionClass
variable {p:Shape} {n N r :ℕ} {A B:Rates}

private theorem echo_pattern (c:PredictionClass) (z:DualCoefficients A B)
    (h:∀ i j,echoes c i j (z.left j) (z.right i))
    (hn:c≠dusk) (he:z.left ≠0∨ z.right≠0):
    z.left=z.right ∧
      ((∃ i, c=dawn i∧ z.left=unary i) ∨ (c=twinned∧ z.left=allSide)) := by
  classical
  have hh (i) : c.active i→ z.left i=z.right i := by
    intro ht; have hk:=(h i i).1
    rcases bit_cases (z.left i) with hi|hi <;> rcases bit_cases (z.right i) with hx|hx <;> simp_all
  cases c
  · exact (hn rfl).elim
  · rename_i i
    have ht : (dawn i).active i:= rfl
    have hact := hh i ht
    have hx j (hij:i≠j): z.left j=0 ∧ z.right j=0 := by
      have hf : ¬(dawn i).active j:=hij
      have h1:=(h i j).1; have h2:=(h j i).1
      constructor
      · exact (bit_cases _).resolve_right fun h'=> hf (h1.mp ⟨h',ht⟩).2
      exact (bit_cases _).resolve_right fun h'=> hf (h2.mpr ⟨h',ht⟩).2
    have hm : z.left=z.right := funext fun j=>by
      by_cases hij : i=j
      · exact hij ▸ hact
      exact (hx j hij).1.trans (hx j hij).2.symm
    have hz:=show z.left≠0 from he.elim id (fun h=>hm.symm ▸ h)
    refine ⟨hm,Or.inl ⟨i,rfl, funext fun j=>?_⟩⟩
    by_cases hij:i=j
    · subst j
      have hv : z.left i=1:= (bit_cases _).resolve_left (fun h=> hz (funext fun j=> by
        by_cases hi : i = j
        · exact hi ▸ h
        exact (hx j hi).1))
      simp [unary,hv]
    rw [(hx j hij).1]; simp [unary,Ne.symm hij]
  · have heq : z.left=z.right:= funext (fun i=> hh i trivial)
    have hz:=show z.left≠0 from he.elim id (fun h=>heq.symm ▸ h)
    refine ⟨heq,Or.inr ⟨rfl,funext fun j=>?_⟩⟩
    change z.left j=1; refine (bit_cases _).resolve_left (fun ht=>?_); apply hz
    apply funext; intro i
    have hx:= (h i j).1
    change z.left i=0; apply (hh i trivial).trans
    exact (bit_cases _).resolve_right (fun h=> zero_ne_one (ht.symm.trans (hx.mpr ⟨h,trivial⟩).1))
  have heq : z.left=z.right:=funext fun i=>hh i trivial
  exfalso
  have hz : z.left ≠0 := he.elim id (heq.symm ▸ id)
  apply hz
  apply funext; intro i; change z.left i=0
  refine (bit_cases _).resolve_right fun hx=>?_
  have ht:= (h (!i) i).2 ⟨hx,trivial⟩
  cases i <;> simp at ht

private theorem gamma_unique {u:Wgt (Fin r)} (w:Fin r→F) (a b:F)
    (hu:IsLaw u) {ε:ℝ} (h:2*ε<1)
    (ha:pr u (fun x=>w x≠a)≤ ε) (hb:pr u (fun x=>w x≠b)≤ ε):
    a=b := by
  classical
  by_contra hf
  have hi (i) (h:True): w i≠a∨w i≠b:=by
    by_cases hh:w i=a
    · exact Or.inr (hh ▸ hf)
    exact Or.inl hh
  have hp:=((pr_mono hu.nz hi).trans (pr_or_le hu.nz)).trans (add_le_add ha hb)
  rw [pr_true,hu.total,←two_mul] at hp
  linarith only [hp,h]

def chorusClass (p:Shape) (v:PredictionData p A B r) (u:Terrain p r) (c:PredictionClass) (τ :ℝ) :=
  c.lit v.α ∧
    (c=dusk→∀ i l q k,v.g i l q k=0) ∧
    ∀ (z:DualCoefficients A B), c≠dusk →
      (∀ i,z.hed i=z.left i.2 * firstBit v.α i.1 ∧ z.hed i=z.right i.1*firstBit v.α i.2) →
      (∀ i l q, ChorusCost v z i u l q≤τ) →
      ∀ i j,c.echoes i j (z.left j) (z.right i)

set_option maxHeartbeats 1400000 in
theorem harmony (v:PredictionData p A B r) (u:Terrain p r) (c:PredictionClass) (τ :ℝ)
    (m:BMark p n N) (x y:UnitType p n N)
    (T:Cross p n) (s:Charts p n A) (t:Charts p n B)
    (hx:coordSpec m x s v.X) (hy:coordSpec m y t v.Y)
    (hg:3≤p.g)
    (h:chorusClass p v u c τ)
    (hq:∀ l q,IsLaw (u l q))
    (he:glint p (m x)=glint p (m y))
    (hf:c.compatible v.α (glint p (m x)) (cardTone m x T,cardTone m y (reciprocal p T)))
    (z:DualCoefficients A B) (hτ:0≤τ) (ht:2*τ<1) (hz:z.left≠0∨z.right≠0)
    (ha:∀ i,z.north i=z.left i.2 • v.X i.1 ∧ z.south i=z.right i.1 •v.Y i.2)
    (hb:∀ i,z.hed i=z.left i.2*firstBit v.α i.1∧z.hed i=z.right i.1*firstBit v.α i.2)
    (hl:∀ i l q,ChorusCost v z i u l q≤τ):
    ∑ i,z.bet i (hailing p s t T i)=0 := by
  classical
  let G:= z.left; let H:=z.right
  let L i j:= contract p T i j (m x i)+role p n (m x i)
  let R i j:= contract p (reciprocal p T) j i (m y j)+role p n (m y j)
  let P:=cardTone m x T; let Q:=cardTone m y (reciprocal p T)
  let D:=glint p (m x)
  have h1 (i j): z.bet (i,j) (hailing p s t T (i,j)) =
      z.gam (i,j) + z.hed (i,j) + (G j * L i j + H i * R i j) := by
    unfold DualCoefficients.bet
    rw [(ha _).1,(ha _).2]; dsimp only [hailing]
    rw [smul_dotProduct,smul_dotProduct,mul_one,mul_one,dotProduct_comm (v.X _),dotProduct_comm (v.Y _)]
    unfold targetMark; rw [←roll_project, ←roll_project,hx _,hy _]; rfl
  let E:=∑ i:Grid,z.gam i
  let F' :=∑ i:Grid,z.hed i
  let g i:=G i*(P i+D); let h' i:=H i*(Q i+D)
  have hZ :∑ i,z.bet i (hailing p s t T i)=E+F'+((∑ i,g i)+(∑ j,h' j)):= by
    have h2 j : ∑ i:Nodes,G j*L i j=g j:= by
      unfold g P L; rw [←Finset.mul_sum,Finset.sum_add_distrib]; rfl
    have h3 i:∑ j:Nodes,H i*R i j=h' i:= by
      unfold h' Q R D; rw [←Finset.mul_sum,Finset.sum_add_distrib,he]; rfl
    unfold E F'; rw [Fintype.sum_prod_type, Fintype.sum_prod_type,Fintype.sum_prod_type]
    simp_rw [h1,Finset.sum_add_distrib,h3]
    congr 2
    rw [Finset.sum_comm]; simp_rw [h2]
  let l : Tag p.g:=⟨0,by omega⟩; let w:= u l 1
  have hh i: pr w (fun k=>G i.2 *v.g i.1 l 1 k+H i.1*v.g i.2 l 1 k ≠ z.gam i)≤τ :=by
    simpa only [w,ChorusCost,G,H,mul_one] using hl i l 1
  rw [hZ]
  by_cases hC : c=dusk
  · subst c
    have hg i : z.gam i=0:= by
      apply gamma_unique (w:=fun k=>_) _ _ (hq l 1) ht (hh i)
      simp only [h.2.1 rfl,mul_zero,add_zero, ne_eq,not_true_eq_false,pr_false]
      exact hτ
    have hf' i : z.hed i=0:= by
      rw [(hb i).1,h.1.1 i.1 not_false,mul_zero]
    have hx : P=fun _=> D:= congrArg Prod.fst hf
    have hy : Q=fun _=> D:= congrArg Prod.snd hf
    simp only [E,F',hg,hf',g,h',hx,hy,char_two,mul_zero,sum_const_zero]
  have hi := h.2.2 z hC hb hl
  obtain ⟨hr,hG⟩:=echo_pattern c z hi hC hz
  have hm : G=H :=hr
  have hf0 i: z.gam (i,i)=0:= by
    apply gamma_unique (w:=fun k=>_) _ _ (hq l 1) ht (hh (i,i))
    simp only [hm,char_two,ne_eq,not_true_eq_false,pr_false]
    exact hτ
  have hg1 i j : z.gam (i,j)=z.gam (j,i):= by
    apply gamma_unique (w:=fun k=>_) _ _ (hq l 1) ht (hh (i,j))
    simpa only [hm,add_comm] using hh (j,i)
  have hE : E=0 := by unfold E; rw [Fintype.sum_prod_type]
                                ; simp only [Fintype.sum_bool,hf0,hg1 false true,add_zero,zero_add,char_two]
  rw [hE,zero_add]
  obtain ⟨i,hc,hx⟩|⟨hc,hx⟩:=hG
  · subst c
    have hy : H=unary i:=hm ▸ hx
    change P i+Q i=firstBit v.α i at hf
    unfold F'
    rw [Fintype.sum_prod_type]; simp_rw [(hb _).1]
    have hi : firstBit v.α (!i)=0:= h.1.1 _ (by cases i <;> simp [active])
    cases i
    · change firstBit v.α true=0 at hi
      simp [hx,g,h',G,hy,unary,hi]
      rw [add_add_add_comm,char_two,add_zero,hf,char_two]
    · change firstBit v.α false=0 at hi
      simp [hx,g,h',G,hy,unary,hi]
      rw [add_add_add_comm,char_two,add_zero,hf,char_two]
  · subst c
    have hy : H=allSide:=hm ▸ hx
    change dotProduct allSide P + dotProduct allSide Q=0 at hf
    simp only [dotProduct,Fintype.sum_bool,allSide,one_mul] at hf
    unfold F'
    rw [Fintype.sum_prod_type]; simp_rw [(hb _).1]
    simp only [hx,g,h',G,hy,Fintype.sum_bool,allSide,one_mul,char_two,zero_add]
    rw [add_add_add_comm (P true) D,add_add_add_comm (Q true) D,char_two]
    simpa using hf
end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
