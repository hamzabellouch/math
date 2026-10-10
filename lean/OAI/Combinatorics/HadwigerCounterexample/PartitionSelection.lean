import OAI.Combinatorics.HadwigerCounterexample.WeightedPartitions

namespace OAI

/-! # Partition Selection -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

abbrev CTile (p : Shape) (n N : ℕ) := Finset (UnitType p n N)
abbrev Canopy (p : Shape) (n N : ℕ) := Tiles (UnitType p n N)

structure Ripe (p : Shape) {n N} (w μ : Wgt (UnitType p n N))
    (S : CTile p n N) (a : Pin p n N) (D ζ : ℝ) (K : ℕ) : Prop where
  pos : 0 < partMass w S
  fixpin : ∀ x∈ S,a.agree x
  bound : planRank a.sp≤K
  clear : a.clear ζ (partW w S)
  density x : partW w S x ≤ bp (D*N) * μ x

variable {w μ : Wgt (UnitType p n N)}

def dustPin (p : Shape) (n N : ℕ) : Pin p n N := Pin.make ⊥ 0

theorem first_ripe {ζ D : ℝ} {K : ℕ} (hz : 0 < ζ) (hz' : ζ < 1) (hn : 0<N)
    (hR : ∀ a : Pin p n N, pr μ a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hc : ∀ x, w x ≤ bp (D*N) * μ x) (hw : ∀ x, 0 ≤ w x)
    (R : CTile p n N) (hK : D + ζ ≤ (ζ-ζ/4)*K) :
    ∃ T : Canopy p n N,apart T ∧ (∀ S∈T,S⊆R ∧ ∃ b,Ripe p w μ S b (D+K+1) ζ K) ∧
      pr w (fun x => x∈R ∧ ¬ inTiles T x) ≤ bp (-ζ*N) := by
  let a := dustPin p n N
  have h x : a.agree x := by
    intro i v hv
    have hl : v = 0 := show v∈(⊥:Space _) from hv
    rw [hl,Matrix.mulVec_zero,Matrix.mulVec_zero]
  obtain ⟨T,hT,hU,hW⟩ := peel_family hz hz' hn hR hc hw R a (fun i _ => h i) hK
  have he : planRank a.sp=0 := Finset.sum_eq_zero (fun i _ => finrank_bot ..)
  refine ⟨T,hU,fun S h => ?_,hW⟩
  obtain ⟨hh,b,hb⟩ := hT S h
  exact ⟨hh,b,hb.pos,hb.fixpin,by simpa only [he,zero_add] using hb.bound,hb.clear,hb.density⟩

theorem ripe_restrict (hw : ∀ x,0≤w x) {S Y} {a : Pin p n N} {D ζ : ℝ} {K : ℕ}
    (h : Ripe p w μ S a D ζ K) (hz : 0≤ζ) (he : Y⊆S)
    (hp : bp (-ζ*N) ≤ partMass (partW w S) Y) :
    Ripe p w μ Y a (D+ζ) (2*ζ) K := by
  classical
  let v := partW w S
  have hv : IsLaw v := on_law hw h.pos
  have ht := lt_of_lt_of_le (bp_pos _) hp
  have hh := on_mon hv.nz (bp_pos _) hp
  obtain ⟨h1,h2⟩ := issued_law w hw h.pos he ht
  have hk (x) : partW w Y x ≤ bp (ζ*N) * v x := by
    rw [h2]
    have hg := hh x
    rw [neg_mul,bp_neg, inv_inv] at hg
    exact hg
  have hy : IsLaw (partW w Y) := on_law hw h1
  refine ⟨h1,fun x hx => h.fixpin x (he hx),h.bound,fun b => ?_,fun x => ?_⟩
  · let r := planNew a.sp b.sp
    by_cases hr : r=0
    · change pr _ _ ≤ fee N _ r
      rw [hr]
      simp only [fee,Nat.cast_zero,mul_zero,zero_mul,bp_zero]
      exact (pr_le_tot hy.nz).trans hy.total.le
    apply ((pr_cap hk _).trans
      (mul_le_mul_of_nonneg_left (h.clear b) (bp_pos _).le)).trans
    change bp (ζ*N)*fee N ζ r ≤ fee N (2*ζ) r
    rw [fee,fee,←bp_add]
    apply bp_le
    have hh : 1≤(r:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
    have he := mul_le_mul_of_nonneg_right hh (mul_nonneg hz
      (show 0≤(N:ℝ) from Nat.cast_nonneg _))
    linarith only [he]
  exact ((hk x).trans (mul_le_mul_of_nonneg_left (h.density x) (bp_pos _).le)).trans_eq
    (by rw [add_mul,bp_add]; ring)

theorem trim (P : UnitType p n N→Prop) (hw : ∀ x,0≤w x) {D ζ : ℝ} (hz : 0≤ζ) {K}
    {T : Canopy p n N} (hT : apart T) (g : CTile p n N → Pin p n N)
    (h : ∀ i∈T,Ripe p w μ i (g i) D ζ K) :
    ∃ V : Canopy p n N,apart V ∧
    (∀ S∈V,∃ i∈T,S⊆i ∧ Ripe p w μ S (g i) (D+ζ) (2*ζ) K ∧ ∀ x∈S,P x) ∧
    pr w (fun x => inTiles T x ∧ P x ∧ ¬inTiles V x) ≤ allMass w T*bp (-ζ*N) := by
  classical
  refine improve T w hw P (fun i S => Ripe p w μ S (g i) (D+ζ) (2*ζ) K ∧ ∀ x∈S,P x)
    hT (fun i hi => ?_)
  let S := i.filter P
  have hs : S⊆i := Finset.filter_subset _ _
  let v := partW w i
  by_cases he : bp (-ζ*N) ≤ partMass v S
  · refine ⟨{S},?_,?_,?_⟩
    · intro x S h T h'; rw [mem_singleton.mp h,mem_singleton.mp h']; simp only [implies_true]
    · intro j hj; rw [mem_singleton.mp hj]
      exact ⟨hs,ripe_restrict hw (h i hi) hz hs he,fun x h => (mem_filter.mp h).2⟩
    have hh : (fun x => x∈i∧ P x∧ ¬inTiles ({S}:Tiles _) x)=(fun _ => False) := by
      ext x; simp [S,inTiles]; tauto
    rw [hh,pr_false]; exact (bp_pos _).le
  refine ⟨∅,by intro x S h; simp at h, by simp,?_⟩
  have hh (x : UnitType p n N) : x∈S ↔ x∈i∧ P x := by simp [S]
  have hn := le_of_not_ge he
  unfold partMass at hn
  simp_rw [hh] at hn
  simpa [inTiles,v] using hn

variable {I : Type} [Fintype I]

set_option maxHeartbeats 700000 in
theorem reparts (w μ : Wgt (UnitType p n N))
    (hw : IsLaw w) (S : CTile p n N) (D ζ u : ℝ) (hn : 0<N)
    (hz : 0 < ζ) (hz' : ζ < 1)
    (hMu : ∀ a : Pin p n N, pr μ a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hc : ∀ x, w x ≤ bp (D*N)*μ x)
    (f : UnitType p n N → I) (K1 K2 : ℕ)
    (P : CTile p n N → Pin p n N → Prop)
    (h : ∀ i : I, ∃ b : Pin p n N,
       (∀ x∈ S,f x=i → b.agree x) ∧ planRank b.sp ≤ K1 ∧
       ∀ (c : Pin p n N) (G : CTile p n N), G.Nonempty → (∀ x∈G,x∈S ∧ f x=i) → b.sp ≤ c.sp → P G c)
    (hK : (D+u) + ζ ≤ (ζ-ζ/4)*K2) :
    ∃ V : Canopy p n N, apart V ∧ (∀ G∈V,
      G⊆S ∧ ∃ b,Ripe p w μ G b (D+u+K2+1) ζ (K1+K2) ∧ P G b) ∧
      pr w (fun x => x∈S∧ ¬inTiles V x)≤
        (num I*bp (-u*N)) + bp (-ζ*N) := by
  classical
  let X := UnitType p n N
  let F (i : I) := S.filter (fun x => f x=i)
  have hF (i : I) (x : X) : x∈F i ↔ x∈ S ∧ f x=i := mem_filter
  choose b hb hL hP using h
  let R (G : Finset X) (b : Pin p n N) := Ripe p w μ G b (D+u+K2+1) ζ (K1+K2) ∧ P G b
  let C := bp (-ζ*N); let t := bp (-u*N)
  have ht (i : I) :
      ∃ V : Tiles X, apart V ∧ (∀ G∈V,G⊆F i∧∃ b,R G b) ∧
        pr w (fun x => x∈F i ∧ ¬inTiles V x)≤t+partMass w (F i)*C := by
    let S' := F i
    let v := partW w S'
    by_cases hi : t≤partMass w (F i)
    · have ht := lt_of_lt_of_le (bp_pos _ : 0<t) hi
      have hv : IsLaw v := on_law hw.nz ht
      have hx (x) : v x≤bp ((D+u)*N)*μ x := by
        apply ((on_mon hw.nz (bp_pos _) hi x).trans
          (mul_le_mul_of_nonneg_left (hc x) (inv_pos_of_pos (bp_pos _)).le)).trans_eq
        rw [add_mul,bp_add,neg_mul,bp_neg,inv_inv]; ring
      obtain ⟨G,hG,hA,hB⟩ :=
        peel_family hz hz' hn hMu hx hv.nz S' (b i)
          (fun x h => hb i x ((hF ..).mp h).1 ((hF ..).mp h).2) hK
      refine ⟨G,hA,fun S h => ?_,?_⟩
      · obtain ⟨hh,b',hp⟩ := hG S h
        obtain ⟨hz,hzm,_⟩ := exists_of_pr_pos hv.nz hp.pos
        obtain ⟨h1,h2⟩ := issued_law w hw.nz ht hh hp.pos
        refine ⟨hh,b',⟨h1,hp.fixpin,(hp.bound.trans (Nat.add_le_add_right (hL _) _)),?_,?_⟩,
          hP i _ _ ⟨hz,hzm⟩ (fun x hx => (hF ..).mp (hh hx)) hp.extendsSp⟩
        · rw [h2]; exact hp.clear
        rw [h2]; exact hp.density
      · rw [pr_of_on hw.nz (fun x => x∈ F i)]
        have hh : pr v (fun x => ¬inTiles G x) = pr v (fun x => x∈F i ∧ ¬inTiles G x) := by
          apply avg_congr
          intro x h; simp only [show x∈F i from (onW_ne h).1,true_and]
        refine le_trans (mul_le_mul_of_nonneg_left (hh.trans_le hB) ht.le) ?_
        exact le_add_of_nonneg_left (bp_pos _).le
    · refine ⟨∅,(fun x S h => ?_),by simp,?_⟩
      · simp at h
      apply le_trans (pr_mono hw.nz (q:=fun x => x∈F i) fun _ => And.left)
        ((le_of_not_ge hi).trans ?_)
      exact le_add_of_nonneg_right (mul_nonneg (pr_nonneg hw.nz) (bp_pos _).le)
  choose V hV h1 h2 using ht
  let G := Finset.univ.biUnion V
  refine ⟨G,?_,?_,?_⟩
  · intro x S hS T hT h hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hT
    obtain rfl : i=j := ((hF ..).mp ((h1 i S hi).1 h)).2.symm.trans
      ((hF ..).mp ((h1 j T hj).1 hx)).2
    exact hV i x S hi T hj h hx
  · intro S h
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨h,h'⟩ := h1 i S hi
    exact ⟨h.trans (Finset.filter_subset _ _),h'⟩
  · let Q (i : I) := fun x : X => x∈ F i ∧ ¬inTiles (V i) x
    have hf x (h : x∈ S∧¬inTiles G x) : ∃ i,Q i x := by
      refine ⟨f x,(hF ..).mpr ⟨h.1,rfl⟩,?_⟩
      rintro ⟨T,hT,h'⟩
      exact h.2 ⟨T,Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ (f x),hT⟩,h'⟩
    refine ((pr_mono hw.nz hf).trans ((pr_exists_le hw.nz Q).trans
      (Finset.sum_le_sum fun i _ => h2 i))).trans ?_
    rw [Finset.sum_add_distrib]
    have ht : (∑ i, partMass w (F i)) ≤ 1 := by
      simp_rw [partMass, hF,sum_pr_tag]
      exact (pr_le_tot hw.nz).trans hw.total.le
    calc (∑ _ : I,t)+∑ i,partMass w (F i)*C ≤ num I*t+1*C := by
           rw [← Finset.sum_mul]
           simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,num]
           exact add_le_add_right (mul_le_mul_of_nonneg_right ht (bp_pos _).le) _
         _ = _ := by rw [one_mul]

end HadwigerCounterexample

end

end OAI
