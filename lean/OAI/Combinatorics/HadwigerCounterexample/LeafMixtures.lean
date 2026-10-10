import OAI.Combinatorics.HadwigerCounterexample.PartitionDeletionBounds
import OAI.Combinatorics.HadwigerCounterexample.RefinedPinImages

namespace OAI

/-! # Leaf Mixtures -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap Filter
open scoped BigOperators
variable {p : Shape} {n N M : ℕ}
structure LeafMixture (p : Shape) (n N : ℕ) where
  T : Canopy p n N
  pin : CTile p n N → Pin p n N

namespace LeafMixture
abbrev X (p : Shape) (n N : ℕ) := UnitType p n N

instance : Inhabited (LeafMixture p n N) := ⟨⟨∅,fun _=>dustPin ..⟩⟩

def poller (s : LeafMixture p n N) (x : X p n N) : Pin p n N :=
  open scoped Classical in
  if h : inTiles s.T x then s.pin h.choose else dustPin p n N

theorem poller_eq (s : LeafMixture p n N) (h : apart s.T) {x i} (hi : i∈s.T) (hx : x∈i) :
    s.poller x=s.pin i := by
  classical
  have hc : inTiles s.T x := ⟨_,hi,hx⟩
  unfold poller; rw [dite_eq_left hc,h _ _ hc.choose_spec.1 _ hi hc.choose_spec.2 hx]

def rooting (s : LeafMixture p n N) (x : X p n N) := (s.poller x).sp
def amount (s : LeafMixture p n N) (w : Wgt (X p n N)) := allMass w s.T
def sap (s : LeafMixture p n N) (w : Wgt (X p n N)) := allW w s.T

variable {s : LeafMixture p n N} {w μ : Wgt (X p n N)}
structure strength (s : LeafMixture p n N) (w μ : Wgt (X p n N)) (D ζ : ℝ) (K : ℕ) : Prop where
  part : apart s.T
  leaf : ∀ i∈s.T,Ripe p w μ i (s.pin i) D ζ K
variable {D E ζ η : ℝ} {K L : ℕ}

theorem root_bound (hh : strength s w μ D ζ K) (x : X p n N) : planRank (s.rooting x) ≤ K := by
  classical
  by_cases hs : inTiles s.T x
  · rw [rooting,poller,dite_eq_left hs]
    exact (hh.leaf _ hs.choose_spec.1).bound
  unfold rooting poller; rw [dite_eq_right hs]
  exact le_of_eq_of_le (Finset.sum_eq_zero (fun i _=>finrank_bot ..)) K.zero_le

theorem strength.slide (h : strength s w μ D ζ K) (hD : D≤E) (hζ : ζ≤η)
    (hk : K≤L) (hμ : ∀ x,0≤μ x) : strength s w μ E η L := by
  classical
  refine ⟨h.part,fun i hi=>?_⟩
  have hh:=h.leaf _ hi
  refine ⟨hh.pos,hh.fixpin,hh.bound.trans hk,fun b=>?_,fun x=>?_⟩
  · refine (hh.clear b).trans (bp_le ?_)
    gcongr
  exact (hh.density x).trans (mul_le_mul_of_nonneg_right (bp_le (by gcongr)) (hμ _))

theorem sapLaw (h : 0<s.amount w) (hw : IsLaw w) : IsLaw (s.sap w) := on_law hw.nz h

def within (s : LeafMixture p n N) (P : X p n N→Prop) := ∀ i∈ s.T,∀ x∈ i,P x
theorem in_parent {P : X p n N → Prop} (h : s.within P) {x} (he : inTiles s.T x) : P x :=
  h he.choose he.choose_spec.1 _ he.choose_spec.2
theorem present {x} (h : s.sap w x≠0) : inTiles s.T x ∧ w x≠0 := onW_ne h

theorem upper_sap (hw : IsLaw w) (hp : 0<s.amount w) (x) :
    s.sap w x ≤ (s.amount w)⁻¹*w x :=
  on_mon hw.nz hp le_rfl x
theorem upperSide {N n} {Lr K' : ℝ} {w v : Wgt (X p n N)} {m : Mixer p n} (hp : bySide p w m Lr)
    {Lr' : ℝ} (h : ∀ x,v x≤K'*w x) (hk : 0≤K') (hh : K'*Lr ≤ Lr') :
    bySide p v m Lr' := by
  intro i x
  refine (mapW_cap h _ x).trans ?_
  calc _ ≤ K'*(Lr*raw m N x) := mul_le_mul_of_nonneg_left (hp i _) hk
       _ ≤ _ := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hh (raw_nonneg m _)

/-- first rural pack. -/
theorem grove_first (ζ D : ℝ) (K : ℕ) (hz : 0<ζ) (hz' : ζ < 1)
    (hn : 0<N)
    (hR : ∀ a : Pin p n N, pr μ a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hc : ∀ x,w x ≤ bp (D*N)*μ x)
    (hw : ∀ x,0≤w x) (P : X p n N→Prop)
    (hK : D+ζ ≤ (ζ-ζ/4)*K) :
    ∃ s : LeafMixture p n N,s.strength w μ (D+K+1) ζ K ∧ s.within P ∧
      pr w P-bp (-ζ*N) ≤ s.amount w := by
  classical
  let R := Finset.univ.filter P
  have hr (x : X p n N) : x∈R↔ P x := by simp [R]
  obtain ⟨T,ht,hg,h⟩:= first_ripe hz hz' hn hR hc hw R hK
  choose a ha using (show ∀ S:CTile p n N,∃ a,S∈T→Ripe p w μ S a (D+K+1) ζ K from
    fun S=>by
      by_cases hs : S∈T
      · obtain ⟨x,h⟩:=(hg S hs).2; exact ⟨x,fun _=>h⟩
      exact ⟨dustPin ..,fun hh=>(hs hh).elim⟩)
  let s : LeafMixture p n N := ⟨T,a⟩
  refine ⟨s, ⟨ht,fun x hx=>ha x hx⟩,fun i hi x hx=>(hr x).mp ((hg _ hi).1 hx),?_⟩
  simp_rw [hr] at h
  let Q (x : X p n N) := P x ∧ ¬inTiles T x
  have hv (x : X p n N) : P x → inTiles T x ∨ Q x := by unfold Q; tauto
  have hh : pr w P≤s.amount w+bp (-ζ*N) :=
    ((pr_mono hw hv).trans (pr_or_le hw)).trans (add_le_add_right h _)
  linarith

def elder (s t : LeafMixture p n N) (P : X p n N→Prop)
    (S : CTile p n N → CTile p n N → Prop) :=
  ∀ i ∈ t.T, ∃ i'∈ s.T,i⊆i' ∧ (∀ x∈i,P x) ∧ S i i'
theorem ancestral {s t : LeafMixture p n N} {P Q}
    (he : elder s t P Q) {x} (h : inTiles t.T x) : inTiles s.T x∧P x := by
  obtain ⟨j,hj,hx⟩ := h
  obtain ⟨i,hi,hs,hp,_⟩ := he j hj
  exact ⟨⟨_,hi,hs hx⟩,hp x hx⟩
theorem elder_trim {s : LeafMixture p n N} (h : strength s w μ D ζ K) (hz : 0≤ζ)
    (hw : IsLaw w) (P : X p n N→Prop) :
    ∃ t : LeafMixture p n N, t.strength w μ (D+ζ) (2*ζ) K ∧
      elder s t P (fun i j=>t.pin i=s.pin j) ∧
      pr w (fun x=>inTiles s.T x∧P x∧¬inTiles t.T x)≤ bp (-ζ*N) := by
  classical
  obtain ⟨T,ht,hg,hf⟩:= trim P hw.nz hz h.part s.pin h.leaf
  let f (i : CTile p n N) := if hi:i∈T then (hg i hi).choose else ∅
  let t : LeafMixture p n N := ⟨T,fun i=>s.pin (f i)⟩
  have he (i : CTile p n N) (hi : i∈T) :
      f i∈s.T ∧ i⊆ f i ∧ Ripe p w μ i (s.pin (f i)) (D+ζ) (2*ζ) K ∧ ∀ x∈i,P x := by
    unfold f; rw [dite_eq_left hi]; exact (hg i hi).choose_spec
  exact ⟨t,⟨ht,fun i hi=>(he i hi).2.2.1⟩,fun i hi=>by
    obtain ⟨h,h1,h2,h3⟩:= he i hi; exact ⟨_,h,h1,h3,rfl⟩,
    hf.trans (by
      have hi : allMass w s.T ≤1 := (pr_le_tot hw.nz).trans hw.total.le
      exact (mul_le_mul_of_nonneg_right hi (bp_pos _).le).trans_eq (one_mul _))⟩

set_option maxHeartbeats 800000 in
theorem elder_weave {s : LeafMixture p n N} (h : strength s w μ D ζ K) (hz : 0<ζ)
    (hw : IsLaw w) (P : X p n N→Prop)
    {u : ℝ} {K' d : ℕ}
    (m : BMark p n N) (T : Cov p N)
    (hz' : ζ<1) (hn : 0<N)
    (hμ : ∀ a : Pin p n N,pr μ a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hd : cdim p T≤ d)
    (hg : ∀ i∈s.T,∀ x∈i,P x → covered p T (delta m x) ∧ ∀ j,m x j∈effective (s.pin i).sp j)
    (hk : D+u+ζ≤(ζ-ζ/4)*K')
    (hu : (3*d+2*K:ℝ)*N+2*K^2 ≤ (u-1)*N) :
    ∃ t : LeafMixture p n N, t.strength w μ (D+u+K'+1) ζ (3*K+K') ∧
      elder s t P (fun i j => specialLeaf T m (s.pin j) i (t.pin i)) ∧
      pr w (fun x=>inTiles s.T x∧P x∧¬inTiles t.T x)≤ bp (-(N:ℝ))+bp (-ζ*N) := by
  classical
  obtain ⟨V,hV,hX,hF⟩:= weave P m T hw.nz hz hz' hn hμ hd h.part _ h.leaf hg hk hu
  let R (i j : CTile p n N) b := j∈s.T ∧ i⊆j ∧ (∀ x∈i,P x) ∧
    Ripe p w μ i b (D+u+K'+1) ζ (3*K+K') ∧ specialLeaf T m (s.pin j) i b
  choose f h1 using (show ∀ i: CTile p n N,∃ b,i∈V → ∃ j,R i j b from
    fun i=>by
      by_cases hi : i∈ V
      · obtain ⟨j,hj,hp,hc,b,h⟩:= hX i hi
        exact ⟨b,fun _ => ⟨_,hj,hp,hc,h⟩⟩
      exact ⟨dustPin ..,fun hh=> (hi hh).elim⟩)
  refine ⟨⟨V,f⟩,⟨hV,fun i hi=>?_⟩,fun i hi=>?_,hF.trans (by
    have hh : allMass w s.T ≤1 := (pr_le_tot hw.nz).trans hw.total.le
    exact (mul_le_mul_of_nonneg_right hh (add_nonneg (bp_pos _).le (bp_pos _).le)).trans_eq
      (one_mul _))⟩
  · obtain ⟨_,_,_,_,hh,_⟩:= h1 i hi; exact hh
  obtain ⟨_,h',hx,hy,_,hh⟩:= h1 i hi; exact ⟨_,h',hx,hy,hh⟩

end LeafMixture
end HadwigerCounterexample

end

end OAI
