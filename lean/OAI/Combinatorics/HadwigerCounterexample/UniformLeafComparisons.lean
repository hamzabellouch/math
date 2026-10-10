import OAI.Combinatorics.HadwigerCounterexample.LeafSurrogateExperiments

namespace OAI

/-! # Uniform Leaf Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Filter Function Matrix Finset
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p:Shape} {M n N s0 K r:ℕ} {q:Format} {d e:Rates} {b:Bool} {b':PreparationParameters}

namespace Quill
variable (w:Quill p q d b)
  (t:Tagging p (Messenger q)) (z: Messenger q→F)
def accounting (m:Mixer p n) (s:Charts p n d)
    (μ:Wgt (UnitType p n N)) (r : ℕ) (δ R ε η : ℝ) :=
    let Q:= w.custom μ s t z m
    let ν:= lawNu p N t z
    (∀ i,Q i→SubLaw i ∧ lsupp i ν) ∧ roster Q r ε∧smallSet Q ν δ η∧ rosterTail Q ν R η

set_option maxHeartbeats 900000 in
theorem ownCertificate (M:ℕ) (h:AnalyticParameters p M b' s0) (hw : w.moral t z)
    (ε η:ℝ) (he:0<ε) (hη:0<η) :
    ∃ (r:ℕ) (δ R:ℝ),0<δ∧0<R∧ ∀ᶠ n : ℕ in atTop,let N:=M*n;
      ∀ (m:Mixer p n) (s:Charts p n d) (μ:Wgt (UnitType p n N)),
      2*num (Full p n)<(N:ℝ) → IsLaw μ →
        (∀ i,μ i ≤ bp (b'.leafNew*N)*PreparationParameters.usual p m N i) →
        w.accounting t z m s μ r δ R ε η := by
  classical
  let v:= w.pen t
  have hc : 0≤b'.leafNew := by unfold PreparationParameters.leafNew PreparationParameters.leafOld; positivity
  have ht:= h.enter.first
  obtain ⟨r,δ,R,hd,hR,hV⟩:= v.controls M ht.hM Bool b'.leafNew η ε hc hη he
  refine ⟨r,δ,R,hd,hR,?_⟩
  filter_upwards [hV,eventually_ge_atTop (2*p.r)] with n hn ht' N m s μ hN hμ hv
  let u:=w.policies t z n
  have hu i:IsLaw (u i) := Appearance.witLaw (w.allure_apt t z hw i) ht.hR ht'
  have ha := hn m hN μ hμ hv u hu (fun i=>scopedZ_bit p n _ _ _ (hu _))
    (w.billboard (N:=N) s t z m)
  let P:=ownPart (p:=p) (N:=N) t z
  obtain ⟨hh,_,_,hQ⟩:=ha
  have hv : roster (w.custom μ s t z m) r ε∧ smallSet (w.custom μ s t z m) (lawNu p N t z) δ η ∧
      rosterTail (w.custom μ s t z m) (lawNu p N t z) R η := hQ P
  refine ⟨fun i hi=>?_,hv⟩
  obtain ⟨x,hp,rfl⟩:= hi
  refine ⟨subLaw_sub (hh x hp) P,fun i hi=>?_⟩
  have ht:= density_hung P (subW x P) (subW_carried x P) i
  exact left_ne_zero_of_mul (ht.symm ▸ hi)

structure penny (m:Mixer p n) (s:Charts p n d) (μ:Wgt (UnitType p n N))
    (R η ε:ℝ) (r:ℕ) : Prop where
  sales i : w.custom μ s t z m i → SubLaw i∧lsupp i (lawNu p N t z)
  roll : roster (w.custom μ s t z m) r ε
  tailS : rosterTail (w.custom μ s t z m) (lawNu p N t z) R η

theorem pennyLarge (R η ε : ℝ) (r:ℕ) (m:Mixer p n) (s:Charts p n d)
    (μ:Wgt (UnitType p n N)) (h:w.penny t z m s μ R η ε r) {R' : ℝ} {r':ℕ}
    (h1:R≤R') (h2:r≤r') : w.penny t z m s μ R' η ε r' := by
  refine ⟨h.sales,?_,fun f hf=>?_⟩
  · obtain ⟨q,hq,hh⟩:= h.roll; exact ⟨q,hq.trans h2,hh⟩
  exact le_trans (pr_mono (h.sales f hf).1.nz (fun i hi=>h1.trans hi)) (h.tailS f hf)

theorem pennywise (M:ℕ) (h:AnalyticParameters p M b' s0) (hw:w.moral t z) (η:ℝ) (hη:0<η) :
    ∃ R:ℝ,0<R∧∀ ε:ℝ,0<ε→ ∃ r:ℕ,∀ᶠ n : ℕ in atTop,let N:=M*n;
      ∀ (m:Mixer p n) (s:Charts p n d) (μ:Wgt (UnitType p n N)),
      2*num (Full p n)<(N:ℝ) → IsLaw μ →
        (∀ i,μ i ≤ bp (b'.leafNew*N)*PreparationParameters.usual p m N i) →
        w.penny t z m s μ R η ε r := by
  obtain ⟨r,a,R,ha,hR,hV⟩:= w.ownCertificate t z M h hw 1 η zero_lt_one hη
  refine ⟨R,hR,fun ε he=>?_⟩
  obtain ⟨r',d',R',hd,hR',he'⟩:= w.ownCertificate t z M h hw ε η he hη
  refine ⟨r',?_⟩
  filter_upwards [hV,he'] with n hn ht N m s μ hN hμ hl
  obtain ⟨hx,_,_,he⟩:= hn m s μ hN hμ hl
  exact ⟨hx,(ht m s μ hN hμ hl).2.1, he⟩
end Quill

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
omit [Fintype B] [Fintype C] in
theorem rebate_thick (w : Wgt A) (f : A→B) (g : B→C) (h : Injective g) (p q: Wgt A) :
    rebate w p q (g∘f)=rebate w p q f := by
  have ht (a : Wgt A) : banner w (g∘f) a = banner w f a := by
    funext x; unfold banner cashbook mapW
    simp_rw [Function.comp_apply,h.eq_iff]
  unfold rebate; rw [ht,ht]
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
