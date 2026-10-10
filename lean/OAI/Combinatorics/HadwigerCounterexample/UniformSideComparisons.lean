import OAI.Combinatorics.HadwigerCounterexample.CommonPartitionRefinement

namespace OAI

/-! # Uniform Side Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {M n N r s0 : ℕ}
namespace StatusAnalysis
namespace Quill
variable {q : Format} {d : Rates} {b:Bool}
    (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
variable {b' : PreparationParameters}

def matchesArea (Y: Silhouette p N r) (o:UnitType p n N) (δ:ℝ) :=
  ∀ i:Messenger q,(w.allure t z i).close Y (onSide o (parcel b i)) δ
theorem area_mono {o:UnitType p n N} (Y:Silhouette p N r)
    {δ ε:ℝ} (h :w.matchesArea t z Y o δ) (he : δ≤ε) :
    w.matchesArea t z Y o ε := fun i=> (h i).trans he

def flunk (Y: Silhouette p N r) (W:Wgt (Keys (p:=p) t N)) (m: Mixer p n)
    (δ ε:ℝ) (o : UnitType p n N) :=
  PreparationParameters.frameSide p m o ∧ matchesArea w t z Y o δ ∧
    ∃ s : Charts p n d, ε< |w.prowl s t z m o W-w.sheen t z o m s Y W|

private theorem resolve_ready (M:ℕ) (h : AnalyticParameters p M b' s0)
    (hw : w.moral t z) (δ : ℝ) (hd:0<δ) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n, (2*num (Full p n)<(N:ℝ)) →
      binaryGood m → ∀ r:ℕ,∀ Y:Silhouette p N r, ∀ o:UnitType p n N,
      PreparationParameters.frameSide p m o → w.matchesArea t z Y o δ →
      litFire p o → w.mirrorSpan t z m 0 δ Y o := by
  classical
  let v:= w.pen t
  have ht:=h.enter.first; let a:=(scanPrice p)⁻¹
  have ha : 0<a:=inv_pos_of_pos (scanPrice_pos p)
  let L:=2*netFact (trayPort p t)
  let N (n:ℕ):=M*n
  have hz := (trend_sizes atTop (le_refl _) ht.hM).2
  have h1 :
      ∀ᶠ n : ℕ in atTop, a^2*bp (-(n:ℝ)/10) ≤ δ := by
    have he := (bp_nat_vanish (by norm_num : 0<(1/10:ℝ))).const_mul (a^2)
    have hh : ∀ᶠ n:ℕ in atTop,a^2*bp (-(1/10:ℝ)*n) ≤ δ :=
      he.eventually (eventually_le_nhds (by rw [mul_zero]; exact hd))
    filter_upwards [hh] with n hn
    rw [show -(n:ℝ)/10= -(1/10:ℝ)*n from by ring]; exact hn
  have h2 :
      ∀ᶠ n:ℕ in atTop,L*bp (-(N n:ℝ)/2) ≤ δ := by
    have he:=(((bp_tendsto_zero (by norm_num : 0<(1/2:ℝ))).comp hz).const_mul L)
    have hh : ∀ᶠ n:ℕ in atTop,L*bp (-(1/2:ℝ)*(N n:ℝ))≤δ :=
      he.eventually (eventually_le_nhds (by rw [mul_zero]; exact hd))
    filter_upwards [hh] with n hn
    rw [show -(N n:ℝ)/2= -(1/2:ℝ)*(N n:ℝ) from by ring]; exact hn
  filter_upwards [eventually_ge_atTop (2*p.r), h1,h2,hz.eventually
    (eventually_ge_atTop (2*num (Messenger q×Toast p) +1))]
    with n hn hi hj hB N m hN hm r Y o hp hv hf
  let W:=w.policies t z n; let f:=w.allure t z
  have he i: (f i).apt:=w.allure_apt t z hw i
  have hW i : IsLaw (W i):=Appearance.witLaw (he i) ht.hR hn
  have hC i j : W i j ≤ a * unif j := dialCap p _ _ _ ht.hR hn (he i) j
  have hy : v.diffsel := fun i j h _ =>fun ht=>h (hw.1 ht)
  refine ⟨hW,hp,hv,fun z hz=>(v.resonant m hm o hf hy W hW a ha hC w.script z hz).trans hi,
    fun f hf=> (reference_product t z f hf ?_).trans hj⟩
  change _≤(N:ℝ) at hB; linarith only [hB]

def markedTest (M : ℕ) (b' : PreparationParameters) (s0 n : ℕ) {r}
    (X : Silhouette p (M*n) r) (W : Wgt (Keys (p:=p) t (M*n))) (L u ε:ℝ) :=
    let N:=M*n; ∀ r:ℕ,∀ Y:Silhouette p N r,refines Y X →
    ∀ (m : Mixer p n) (U:Wgt (UnitType p n N)), b'.Align s0 p M n m U →
      pr U (w.flunk t z Y W m u ε) ≤ L

set_option maxHeartbeats 1600000 in
theorem sideRelease (M:ℕ) (h : AnalyticParameters p M b' s0) (hw : w.moral t z) (ε:ℝ) (he:0<ε) :
    ∃ (l:ℕ) (u c:ℝ),0<u∧0<c∧∀ᶠ n : ℕ in atTop,let N:=M*n;∀ W:Wgt (Keys (p:=p) t N),
      (∀ x, |W x|≤ 1) → ∃ X: Silhouette p N l,w.markedTest t z M b' s0 n X W (bp (-c*n)) u ε := by
  classical
  let a := ε/4; have ha : 0<a:=by unfold a; positivity
  let v:=w.pen t; have ht := h.enter.first
  obtain ⟨r,c,hc,hV⟩:= weakly v M ht.hM b'.spJoint a 1 ha zero_le_one
  let x:=2+num (Messenger q)
  let u:=a/((r+1:ℝ)*x)
  have hx : 0<x := by unfold x num; positivity
  have hU : 0<u := by unfold u; positivity
  refine ⟨paletteSize (Messenger q) (Fin r),u,c/2,hU,half_pos hc,?_⟩
  filter_upwards [hV, resolve_ready w t z M h hw u hU, litFire_calendar p b'.spJoint M h.thickness,
    pay_nat (a:=c) 2 (half_lt_self hc),tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (8*c))] with n hn hR hG hQ hD N W hW
  obtain ⟨Z,⟨F,hf,hf'⟩,hM,h⟩:= hn z W hW
  obtain ⟨X,hX⟩:=buildPalette v N z F
  subst Z
  refine ⟨X,?_⟩; intro r' Y hy m U hm
  let P := w.flunk t z Y W m u ε
  let μ:= w.policies t z n
  have hμ i : IsLaw (μ i) := Appearance.witLaw (w.allure_apt t z hw i) ht.hR hm.age
  let T := exceeds v z ((show Wgt (Keys (p:=p) v.t (M*n)) from W)-mural v F) w.script m μ a
  let Q (o:UnitType p n N) := ¬ litFire p o
  have hi o (h : P o) : T o ∨ Q o := by
    by_contra! hh
    obtain ⟨hj,hv,s,h⟩:=h
    have heq : w.witnessPaint t z m a W (mural v F) o :=
      ⟨fun f hf=>hM f hf, hh.1⟩
    have hg := bare_bridge w t z m Y o s F (fun i=> finerPigment X Y hy _ (hX _))
      (by linarith only [ht.hG]) ht.hJ hf' (hR m hm.cols hm.rum _ Y o hj hv (not_not.mp hh.2)) W heq
    refine not_lt_of_ge (hg.trans ?_) h
    have hf : (r:ℝ)*(x*u)≤a := by
      have ht : ((r:ℝ)+1)*(x*u) = a := by unfold u; field_simp
      rw [←ht]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    unfold x a at *
    linarith only [hf,he]
  have hU : IsLaw U:=hm.drain.1
  have hT :=
    h m hm.cols U hm.drain w.script μ hμ (fun i=>scopedZ_bit p n _ _ _ (hμ i))
  have hD' : bp (-(n:ℝ)*n/8) ≤ bp (-c*n) := by
    change _ ≤ (n:ℝ) at hD
    apply bp_le
    nlinarith only [mul_le_mul_of_nonneg_right hD (show 0≤ (n:ℝ) from Nat.cast_nonneg _)]
  have hH : pr U Q≤ bp (-c*n) := (hG m hm.cols U hm.drain.2.2.2).trans hD'
  change pr U T≤bp (-c*n) at hT
  exact ((pr_mono hU.nz hi).trans ((pr_or_le hU.nz).trans (add_le_add hT hH))).trans
     (by rw [two_mul] at hQ; exact hQ)

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
