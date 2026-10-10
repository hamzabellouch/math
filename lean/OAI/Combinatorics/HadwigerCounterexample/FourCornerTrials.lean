import OAI.Combinatorics.HadwigerCounterexample.ConditionalFourCorners

namespace OAI

/-! # Four Corner Trials -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem winglaw (p : Wgt I) :
    mapW (draws Bool p) (wingpair I)=pairW p p := by
  classical
  funext i
  obtain ⟨i,rfl⟩ := (wingpair I).surjective i
  rw [mapW_equiv_val, Equiv.symm_apply_apply]
  simp only [draws,prodW,Fintype.prod_bool]; rfl

theorem quart_bound {A B C : Type} (U : Wgt A) (hU : ∀ i, |U i|≤1) (e : A≃B×C) (i) :
    |quart e U i|≤ 1 := by
  unfold quart; rw [Finset.abs_prod]
  exact (Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _=>hU _)).trans_eq (by simp)

namespace Template
variable (v : Template p I)
def protean (v : Template p I) (T : Wgt (Inputs p n I))
    (U : Wgt (Keys (p:=p) v.t N)) (o : UnitType p n N) :=
  fun x => T x*U (v.resultKey o x)

omit [Fintype I] in
theorem quart_prot (v : Template p I) (j : I) (T : Wgt (Inputs p n I))
    (U : Wgt (Keys (p:=p) v.t N)) (o : UnitType p n N)
    (c : Inputs p n I × Inputs p n I) :
    quart (v.chairI j n) (v.protean T U o) c=
      quart (v.chairI j n) T c *quart (v.chairK j N) U
        (Prod.map (v.resultKey o) (v.resultKey o) c) := by
  unfold quart protean
  rw [Finset.prod_mul_distrib]
  simp_rw [key_quoin]

def crane (v : Template p I) (j : I) (T : Wgt (Inputs p n I))
    (U : Wgt (Keys (p:=p) v.t N))
    (w : I → Wgt (Knobs p.g n)) (o : UnitType p n N) :=
  let x:= prodW w
  avg (pairW x x) (quart (v.chairI j n) (v.protean T U o))

set_option maxHeartbeats 1000000 in
theorem crane_mean (v : Template p I) (j : I) (q : I → F) (U : Wgt (Keys (p:=p) v.t N))
    (T : Wgt (Inputs p n I)) (w : I→ Wgt (Knobs p.g n))
    (hw : ∀ i,IsLaw (w i)) (hz : ∀ i,mapW (w i) (freePart p)=unif)
    (m : Mixer p n) (hN : 2*num (Full p n)<N)
    (δ : ℝ) (hδ : 0≤δ) (hU : ∀ i,|U i|≤1) (hT : ∀ i,|T i|≤1)
    (h : chairCut v j U δ) (hW : carried U (ownPart (p:=p) v.t q))
    (k : ℝ) (hk : ∀ i,num (Port v.seam i)≤ k) (hK : 2*k - (N:ℝ) ≤ -1) :
    let μ := raw m N; let W := netFact v.seam
    |avg (pairW μ μ) (v.crane j T U w)| ≤ 2*W * (num (Ports p)*(2*bp (k-N)))+
      W*(δ+bp (-(N:ℝ)/2)) + bp (num Bool*num I-n) := by
  classical
  intro μ W
  let A := UnitType p n N
  let Q (y o) := quart (v.chairI j n) (v.protean T U o) (wingpair (Inputs p n I) y)
  let ρ := pairW μ μ
  let p' := v.doubleP n
  let M := 2*W * (num (Ports p)*(2*bp (k-N)))+ W*(δ+bp (-(N:ℝ)/2))
  have hp : IsLaw ρ := pairW_law (raw_law m hN) (raw_law m hN)
  have hq : 0 ≤ M := by
    have hh : 0<W := netFact_pos
    unfold M; refine add_nonneg ?_ ?_
    · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (by
        apply mul_nonneg (by norm_num) (bp_pos _).le))
    exact mul_nonneg hh.le (add_nonneg hδ (bp_pos _).le)
  have hh (y : Bool→Inputs p n I) :
      |avg ρ (Q y)| ≤ M+ind (¬p'.free y) := by
    let Y := wingpair _ y
    let f := v.glob_inj
    let P := pooled (p'.left ∘ y)
    let Z := database m P P
    let E (x : A) := peekR p v.seam P P (mergeR p x)
    have he (o : A) :
        untwin v N (E o)=Prod.map (v.resultKey o) (v.resultKey o) Y := by
      have hi (i:Bool) : led i (E o)=scatter v.t N (v.resultKey o (y i)) := by
        unfold E P seam
        rw [peek_pooled]; exact double_show v _ _
      apply Prod.ext
      · change (scatter v.t N).symm (led true (E o))=_
        rw [hi,Equiv.symm_apply_apply]; rfl
      change (scatter v.t N).symm (led false (E o))=_
      rw [hi,Equiv.symm_apply_apply]; rfl
    let C := quart (v.chairI j n) T Y
    have hi (o : A) :
        Q y o=C*packSecs v j U (E o) := by
      unfold Q; rw [quart_prot,show Prod.map _ _ _ = _ from (he o).symm]
      rfl
    have ht : |C|≤1 := quart_bound T hT _ _
    by_cases hg : p'.free y
    · have hx : mapW ρ E=rackStation Z N := by
        change mapW _ (peekR p _ _ _ ∘ _) =_
        rw [←mapW_nested,law_mergeR]; exact law_peekR (g:=v.seam) m hN hg.1 hg.2
      rw [ind_zero (by exact fun h=>h hg : ¬ ¬ p'.free y),add_zero]
      have hh : avg ρ (Q y)=C*avg (rackStation Z N) (packSecs v j U) := by
        rw [← hx,mapW_avg,←avg_mul']
        exact avg_congr fun i _=> hi i
      rw [hh,abs_mul]
      exact (mul_le_mul ht (pack_hot v j q U δ hδ hU h hW Z k hk hK)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    rw [ind_one hg]
    refine (avg_bound1 hp _ (fun i=>?_)).trans (le_add_of_nonneg_left hq)
    rw [hi,abs_mul]
    exact (mul_le_mul ht (pack_bound v j U hU _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  let S := draws Bool (prodW w)
  have hr : IsLaw S := draws_law (prodW_law hw)
  have he : avg ρ (crane v j T U w)=avg S (fun y => avg ρ (Q y)) := by
    rw [avg_avg]
    apply avg_congr; intro i _
    change avg (pairW (prodW w) (prodW w)) _=_
    rw [←winglaw (prodW w),mapW_avg]
  rw [he]
  refine (abs_avg_le hr.nz).trans ((avg_mono hr.nz hh).trans ?_)
  rw [avg_add,hr.avg_const]
  exact add_le_add_right (free_price v n w hw hz (globPort p v.t v.aim) (glob_inj v)) _
end Template
end HadwigerCounterexample

end

end OAI
