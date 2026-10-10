import OAI.Combinatorics.HadwigerCounterexample.KeyProjectionBounds

namespace OAI

/-! # Adaptive Projection Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
variable {p:Shape} {n N K M r z s0:ℕ} {q:Format} {d e:Rates} {b:Bool}

private theorem avg_side_bounds {A : Type} [Fintype A] (w : Wgt A) (hw:IsLaw w)
    (b:Bool) (f : Wgt A) (F:A×A→ℝ) (h:∀ i,F i≤f (onSide i b)) :
    avg (pairW w w) F≤avg w f := by
  apply (avg_mono (pairW_law hw hw).nz h).trans
  cases b
  · rw [pairW_avg]
    simp [onSide,hw.avg_const]
  rw [pairW_avg]; simp only [onSide,ite_true,hw.avg_const]; rfl

namespace Quill
variable (w:Quill p q d b)
  (m:Mixer p n) (t:Tagging p (Messenger q)) (φ:Messenger q→F)
  (u:LeafMixture p n N) (Y:Silhouette p N r)

set_option maxHeartbeats 1200000 in
theorem oneTrestle (omega_:Wgt u.T) (hv:IsLaw omega_) (s:u.T→ Charts p n d)
    (μ:u.T→Wgt (UnitType p n N)) (hμ:∀ i,IsLaw (μ i))
    (P : Keys (p:=p) t N→ Fin z) (F:u.T×u.T → UnitType p n N→Prop)
    (hF : ∀ i o,F i o→PreparationParameters.frameSide p m o)
    (hw:∀ i,IsLaw (w.policies t φ n i)) (hν:IsLaw (lawNu p N t φ))
    (ε v A B:ℝ) (he:0≤ε)
    (ha:∀ i:Fin z,
       pr (mixW omega_ μ) (w.flunk t φ Y (fun x=>ind (P x=i)) m v ε) ≤ A)
    (hh: pr (mixW omega_ μ) (fun x=>¬ w.matchesArea t φ Y x v)≤B) :
    let L (i:u.T×u.T):=onSide i b
    avg (pairW omega_ omega_) (fun i=>varOne (mapW (w.displayMass t φ (μ (L i)) (F i) m (s (L i)) Y) P)
       (mapW (w.sales t φ (μ (L i)) (F i) m (s (L i))) P)) ≤ z*(ε+2*(A+B)) := by
  classical
  intro L
  let Q (i:u.T×u.T) (x:Fin z):=
    |mapW (w.displayMass t φ (μ (L i)) (F i) m (s (L i)) Y) P x-
      mapW (w.sales t φ (μ (L i)) (F i) m (s (L i))) P x|
  let V:= pairW omega_ omega_
  have h (x : Fin z) :
      avg V (fun i=>Q i x) ≤ ε+ 2*(A+B) := by
    let H k:= P k=x
    let R:= w.flunk t φ Y (fun i=>ind (H i)) m v ε
    let Z (i:UnitType p n N):= ¬ w.matchesArea t φ Y i v
    let S o:=R o∨ Z o
    have heq (i): Q i x≤ ε+2*pr (μ (L i)) S := by
      refine w.display_test t φ (μ (L i)) (F i) m (s (L i)) Y H (hμ _) hw hν S he
        (fun y hy hz=> ?_)
      by_cases hf :Z y
      · exact Or.inr hf
      exact Or.inl ⟨hF _ _ hy,not_not.mp hf,s (L i),hz⟩
    let U:=mixW omega_ μ
    have hu : IsLaw U:=mixW_law hv hμ
    have hm (o) : avg omega_ (fun i=>pr (μ i) o)= pr U o := (mixW_avg ..).symm
    apply (avg_side_bounds omega_ hv b (fun i=>ε+2*pr (μ i) S) _ heq).trans
    rw [avg_add,avg_mul',hm,hv.avg_const]
    exact add_le_add_right (mul_le_mul_of_nonneg_left ((pr_or_le hu.nz).trans
      (add_le_add (ha _) hh)) (by norm_num)) _
  change avg V (fun x=> ∑ i,Q x i) ≤ _
  rw [avg_sum]; exact (Finset.sum_le_sum fun i _=> h i).trans_eq (by simp; ring)
end Quill

open Station PreparationParameters
namespace Station
variable {w:LeafMixture p n N} (t:Station p n N K w)
    (x:Typus p q d e) (m:Mixer p n) (k: Fin (2^deckMax p K))
    (μ:Wgt (UnitType p n N)) (Y:Silhouette p N r)

theorem gauzed_area (Y:Silhouette p N r) (w : Quill p q d b)
    (t: Tagging p (Messenger q)) (u : Messenger q → F)
    (h:w.moral t u) (δ:ℝ)
    {K : ℕ} {m:Mixer p n} {ε v:ℝ} (he:ε≤v)
    (o : UnitType p n N) (hc:gauze p ε δ Y m K o) :
    w.matchesArea t u Y o v := by
  intro i; have heq := w.allure_apt t u h i
  exact ((hc _ (w.allure t u i)).1 heq).trans he

set_option maxHeartbeats 1200000 in
theorem projectSum (P : Keys (p:=p) x.t N→Fin z)
    (h :apart w.T) (hm:IsLaw μ) (hw :∀ i∈w.T,0<partMass μ i) (hs : 0<w.amount μ)
    (ha : ∀ i,IsLaw (x.qA.policies x.t x.z n i)) (hb:∀ i,IsLaw (x.qB.policies x.t x.z n i))
    (hν : IsLaw (lawNu p N x.t x.z)) (ε v v' τ B δ : ℝ) (he:0≤ε)
    (hf : x.permission)
    (ht : τ ≤ v ∧ τ≤v')
    (hh : pr (w.sap μ) (fun i=>¬gauze p τ δ Y m K i)≤B)
    (hx : ∀ i:Fin z,pr (w.sap μ) (x.qA.flunk x.t x.z Y (fun y=>ind (P y=i)) m v ε)≤B)
    (hy : ∀ i:Fin z,pr (w.sap μ) (x.qB.flunk x.t x.z Y (fun y=>ind (P y=i)) m v' ε)≤B) :
    t.due x m μ k Y P≤2*(z*(ε+2*(B+B))) := by
  classical
  obtain ⟨hp,hq⟩:=rebuild hm.nz h hw hs
  let A (i:w.T):=partW μ i.val
  let u:=portionW μ w.T
  have hQ : w.sap μ=mixW u A :=hq
  let V:=pairW u u; have hA i:IsLaw (A i):=on_law hm.nz (hw i.val i.property)
  have hL : avg V (fun i=> taxLeft t x m μ k Y P i.1 i.2) ≤ z*(ε+2*(B+B)) := by
    refine x.qA.oneTrestle m x.t x.z w Y u hp (fun i=>t.cAxes i d) A hA P
      (fun i=> t.frontPage x m i.1 i.2 k) (fun i o h => h.2.2.1) ha hν ε v B B he
      (fun i=>by rw [←hQ]; exact hx i) ?_
    rw [←hQ]; apply (pr_mono (LeafMixture.sapLaw hs hm).nz ?_).trans hh
    exact fun i hi h=> hi (gauzed_area _ _ _ _ hf.2.1 δ ht.1 i h)
  have hR : avg V (fun i=> taxRight t x m μ k Y P i.1 i.2) ≤ z*(ε+2*(B+B)) := by
    refine x.qB.oneTrestle m x.t x.z w Y u hp (fun i=>t.cAxes i e) A hA P
      (fun i=> t.backPage x m i.1 i.2 k) (fun i o h => h.2.2.1) hb hν ε v' B B he
      (fun i=>by rw [←hQ]; exact hy i) ?_
    rw [←hQ]; apply (pr_mono (LeafMixture.sapLaw hs hm).nz ?_).trans hh
    exact fun i hi h=>hi (gauzed_area _ _ _ _ hf.2.2.1 δ ht.2 i h)
  unfold due; rw [avg_add,two_mul]
  exact add_le_add hL hR

end Station
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
