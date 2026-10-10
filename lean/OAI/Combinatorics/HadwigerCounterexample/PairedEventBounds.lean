import OAI.Combinatorics.HadwigerCounterexample.RareLeafEvents

namespace OAI

/-! # Paired Event Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open Station PreparationParameters
variable {l:Filter ℕ} {b:PreparationParameters} {p:Shape} {M r:ℕ} {m:cycleM p} {s:rhythms p M} {w:tale p M}
    {q:Format} {d e:Rates}

private theorem thick_roster {A:Type} [Fintype A] {P : Wgt A→Prop} {r:ℕ} {ε:ℝ}
    (h:roster P r ε) :
    ∃ f:Fin r→Wgt A,∀ y,P y→∃ i,varOne y (f i)≤ε := by
  classical
  obtain ⟨d,hd,g,hg⟩:=h
  let f(k:Fin r) := if h:k.val<d then g ⟨k.val,h⟩ else 0
  refine ⟨f,fun x h=>?_⟩; obtain ⟨j,hj⟩:=hg x h
  refine ⟨Fin.castLE hd j,?_⟩; unfold f; simpa using hj

set_option maxHeartbeats 2000000 in
theorem dimBerth (t: Stations p M b.pins s)
    (h:veil p M b r l m s w)
    (x:Typus p q d e) (k:Fin (2^deckMax p b.pins)) {β:ℝ} (hβ:0<β) :
    ExpSmall l (fun n=>(n:ℝ)) (fun n=>(t n).berth x (m n) k (w n) β) := by
  classical
  by_cases hX:x.permission
  · let K:=b.pins; let N:=fun n:ℕ=>M*n
    have hq:=h.easel; have hp:= hq.enter.first
    have ha:=hX.2.1; have hb:= hX.2.2.1

    obtain ⟨y,c2,hy,hc2,hB⟩:= x.qB.soberCalendar x.t x.z hq hb 1 zero_lt_one

    let a:=β*y/6; have hα:0<a:=by unfold a; positivity
    obtain ⟨_,δ,_,hd,_,hW⟩:= x.qB.ownCertificate x.t x.z M hq hb 1 a zero_lt_one hα

    obtain ⟨Y,c,hY,hc,hA⟩:= x.qA.soberCalendar x.t x.z hq ha δ hd
    let b0:=β*Y/4; have h0:0<b0:=by unfold b0; positivity

    obtain ⟨_,δ',_,he,_,hF⟩:=x.qA.ownCertificate x.t x.z M hq ha 1 b0 zero_lt_one h0

    let ε:=min a (a*δ')
    have hh:0<ε:=lt_min hα (by positivity)
    obtain ⟨r0,_,_,_,_,hQ⟩:= x.qB.ownCertificate x.t x.z M hq hb ε a hh hα
    let b1:=fun n:ℕ=>bp (-c*n); let b2:=fun n:ℕ=>bp (-c2*n)

    obtain ⟨f,hf,hξ⟩ := h.score_cost t
    let e_ (n:ℕ):=(num (Fin r0)*(b1 n/β)+b2 n/β)
    let D : ℕ→ℝ:=fun n=> e_ n+|f n|/(a*b0)
    have ht:= (trend_sizes l h.timeL hp.hM).2
    have hz : Tendsto (fun n:ℕ=>(n:ℝ)) l atTop := tendsto_natCast_atTop_atTop.mono_left h.timeL
    have hD : ExpSmall l (fun n:ℕ=>(n:ℝ)) D := by
      have h1 := ExpSmall.bp_n (l:=l) (z:=fun i:ℕ=>(i:ℝ)) hc
      have h2:=ExpSmall.bp_n (l:=l) (z:=fun i:ℕ=>(i:ℝ)) hc2
      have hg : ExpSmall l (fun n:ℕ=>(n:ℝ)) e_ := by
        have hi := (h1.mul (expO_const hz (num (Fin r0)/β))).add hz (h2.mul (expO_const hz β⁻¹))
        refine hi.mono (.of_forall (fun i=>?_))
        exact le_of_eq (congrArg abs (by unfold e_ b1 b2; ring))
      obtain ⟨C,hC,hf⟩:= hf
      have h : ExpSmall l (fun n:ℕ=>(n:ℝ)) (fun n=>|f n|) := by
        refine ⟨C*M, by have hm:=hp.hM; positivity,?_⟩
        filter_upwards [hf] with n hn
        rw [abs_abs]; push_cast at hn; rwa [←mul_assoc,neg_mul] at hn
      simpa [D,div_eq_mul_inv] using hg.add hz (h.mul (expO_const hz (a*b0)⁻¹))
    refine hD.mono ?_
    have hl := h.timeL
    filter_upwards [h.upright,h.durableS.shape,h.moment,h.durableS.mass.positive,
       hF.filter_mono hl,hQ.filter_mono hl,hW.filter_mono hl,hB.filter_mono hl,hA.filter_mono hl,hξ,
       ht.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+1))]
       with n hn hr ht hx hf hg hh hB hA hξ hN
    let W:=w n; let s':=s n; let I:=s'.T; let V (i:↑I):=partW W i.val
    let u:=portionW W I; let R:=pairW u u; let G:=t n; let m':=m n
    let ν:= lawNu p (N n) x.t x.z; have hm:=ht.1.law
    let P := s'.sap W
    have hν:IsLaw ν:=nuLaw _ _ (show 2*num (Messenger q×Toast p)-((M*n:ℕ):ℝ)≤ -1 from
      by change _ ≤((M*n:ℕ):ℝ) at hN; linarith only [hN])
    let A i:= x.qA.custom (V i) (G.cAxes i d) x.t x.z m'

    let B i:= x.qB.custom (V i) (G.cAxes i e) x.t x.z m'
    let X(i:↑I×↑I):= leftSales G x m' W i.1 i.2 k
    let Z(i:↑I×↑I):= rightSales G x m' W i.1 i.2 k
    have huv := hr.1
    have hV i : IsLaw (V i):=on_law hm.nz (huv.leaf i.val i.property).pos
    have hC (i:↑I) := (huv.leaf (Subtype.val i) i.property).density
    choose l hL using show ∀ i:↑I,∃ l:Fin r0→Wgt (Keys (p:=p) x.t (N n)),
       ∀ y,B i y→ ∃ j,varOne y (l j) ≤ ε from fun i=>
      thick_roster (hg m' (G.cAxes i e) (V i) hn.cols (hV i) (hC i)).2.1
    obtain ⟨hu,hO⟩:=rebuild hm.nz huv.part (fun i hi=>(huv.leaf _ hi).pos) hx
    have ho : P=mixW u V:= hO
    let S i j:=cliff ν (l i j) a
    let T : UnitType p n (N n)→Prop:= fun i=>¬x.qB.sober x.t x.z K (fun _=>True) m' y i
    let U i j o:= δ ≤ pr ν (S i j) ∧ ¬x.qA.sober x.t x.z K (S i j) m' Y o
    let O (i:↑I×↑I) := (∃ j, β < pr (V i.1) (U i.2 j)) ∨ β < pr (V i.2) T
    have hT : pr R O ≤ e_ n := by
      refine vacantBound u V U T hu hV hβ (fun i j=>?_) ?_
      · by_cases h:δ ≤ pr ν (S i j)
        · simp_rw [U,h,true_and,← ho]; exact hA m' P hn (S i j) h
        have hf : U i j = (fun _=>False) := funext fun i=> eq_false (fun hh=> h hh.1)
        rw [hf,pr_false]; exact (bp_pos _).le
      rw [← ho]
      exact hB m' P hn (fun _=>True) (by rw [pr_true]; exact hν.total.ge)
    let J:=charter (t n) x m' k W β
    let L i := overlap ν (X i) (Z i)
    have hL0 i: IsLaw (x.qA.policies x.t x.z n i):= Appearance.witLaw
       (x.qA.allure_apt x.t x.z ha _) hp.hR hn.age
    have hL1 i:IsLaw (x.qB.policies x.t x.z n i):= Appearance.witLaw
       (x.qB.allure_apt x.t x.z hb _) hp.hR hn.age
    have hX (i:↑I×↑I):A i.1 (X i):= x.qA.sales_custom _ _ _ _ _ _
    have hZ (i:↑I×↑I):B i.2 (Z i):= x.qB.sales_custom _ _ _ _ _ _
    have heq (i) (hj:J i) (hk:¬O i) : a*b0≤ L i := by
      obtain ⟨j,hj'⟩:= hL _ _ (hZ i)
      obtain ⟨hP,_,hX',_⟩:=hf m' (G.cAxes i.1 _) (V i.1) hn.cols (hV _) (hC _)
      obtain ⟨hR',_,hY',_⟩:=hh m' (G.cAxes i.2 _) (V i.2) hn.cols (hV _) (hC _)
      let F:=S i.2 j
      have hFt : δ≤ pr ν F := by
        have hi := x.qB.qualify_hit m' x.t x.z _ _ _ _ (fun _=>True) hy hj.2.2 (hV _) hL1
          (le_of_not_gt (mt Or.inr hk))
        change β*y≤ pr (Z i) _ at hi
        rw [pr_true] at hi
        exact (cliff_thick (B i.2) _ (l i.2 j) ν hν (hZ i) a δ hα hY'
          (hj'.trans (min_le_left ..)) (show 5*a≤tot (Z i) from by unfold a; nlinarith only [hi,hβ,hy])).le
      have hM : β*Y ≤ pr (X i) F :=
        x.qA.qualify_hit m' x.t x.z _ _ _ _ F hY hj.2.1 (hV _) hL0 (le_of_not_gt (fun h=>hk
          (Or.inl ⟨j, by have hf : U i.2 j = fun x_=>¬x.qA.sober x.t x.z K F m' Y x_ := funext fun i=>propext ⟨And.right,fun hi=>⟨hFt,hi⟩⟩; rw [hf]; exact h⟩)))
      obtain ⟨hx,hz⟩:= hP _ (hX i)
      refine cliff_score _ (X i) (Z i) (l i.2 j) ν hx (hR' _ (hZ i)).1 hν hz b0 a ε
        hα (hX i) hj' (fun z hz S hS=> hX' z hz S (hS.trans ?_)) ?_
      · exact (div_le_iff₀ hα).mpr ((min_le_right ..).trans_eq (mul_comm ..))
      change 2*b0 ≤ pr (X i) F
      unfold b0; nlinarith only [hM,hβ,hY]
    have hn0 (i:↑I×↑I) : 0 ≤ L i := by
      have h1 i j : 0≤X i j := Quill.sales_pos x.qA _ _ _ _ m' _ (hV _).nz j
      have h2 i j : 0 ≤ Z i j:= Quill.sales_pos x.qB _ _ _ _ m' _ (hV _).nz j
      refine avg_nonneg hν.nz fun j=>mul_nonneg (div_nonneg (h1 i j) (hν.nz _))
        (div_nonneg (h2 i j) (hν.nz _))
    have hv := pairW_law hu hu
    have hi := le_avg_markov hv.nz hn0 (a*b0)
    change |pr R J| ≤ _
    rw [abs_of_nonneg (pr_nonneg hv.nz)]
    apply le_trans _ (le_abs_self (D n))

    have hg (i) (h:J i): O i ∨ a*b0 ≤ L i := by
      by_cases hi:O i
      · exact Or.inl hi
      exact Or.inr (heq i h hi)
    refine ((pr_mono hv.nz hg).trans (pr_or_le hv.nz)).trans (add_le_add hT ?_)
    refine (le_div_iff₀ (by positivity)).mpr (le_trans ?_ ((le_abs_self _).trans
      ((hξ q d _ x k).trans (le_abs_self _))))
    rw [mul_comm]; exact hi
  · refine (ExpSmall.zero l (fun n=>(n:ℝ))).mono (.of_forall (fun n=>?_))
    have hh i : ¬charter (t n) x (m n) k (w n) β i :=fun he=>hX he.1
    unfold berth pr
    simp only [ind_zero (hh _),avg_const,mul_zero,le_refl]
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
