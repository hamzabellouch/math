import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.PathActivity

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open Finset

variable {V E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]

lemma edge_activity_le_realBottleneck (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (e : E) (i : Fin (4*p+1)) :
    pathActivity p B Hu Hv lam e i ≤ realBottleneck u v p B Hu Hv lam
      (atVertex u v (4*p) e i.castSucc) (atVertex u v (4*p) e i.succ) := by
  apply interval_le_bottleneck u v (4*p) (by omega) huv (pathActivity p B Hu Hv lam) e
    i.castSucc i.succ (by simp)
  intro k hk hk'
  have he : k=i := Fin.ext (by simp only [Fin.val_castSucc,Fin.val_succ] at hk hk'; omega)
  subst k
  exact le_rfl

theorem realBottleneck_noncentral_edge (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 1 ≤ B e)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e) (hlam : ∀ e, lam e ≤ B e)
    (e : E) (i : Fin (4*p+1)) (hi : i.val ≠ 2*p) :
    realBottleneck u v p B Hu Hv lam (atVertex u v (4*p) e i.castSucc)
      (atVertex u v (4*p) e i.succ) = pathActivity p B Hu Hv lam e i := by
  apply le_antisymm _ (edge_activity_le_realBottleneck u v huv p hp B Hu Hv lam e i)
  rcases lt_or_gt_of_ne hi with hi | hi
  · let j : Fin (4*p) := ⟨i.val,by omega⟩
    have hv : atVertex u v (4*p) e i.succ=Sum.inr (e,j) :=
      (atVertex_eq_inr_iff u v (4*p) e e i.succ j).mpr ⟨rfl,rfl⟩
    rw [hv,realBottleneck,bottleneck_comm]
    have hc := realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e j
      (atVertex u v (4*p) e i.castSucc)
    simpa [realBottleneck,pathActivity,internalStrength,show j.val<2*p from hi,
      profile_left p (B e) (Hu e) (Hv e) (lam e) i hi,j] using hc
  · let j : Fin (4*p) := ⟨i.val-1,by have := i.isLt; omega⟩
    have hv : atVertex u v (4*p) e i.castSucc=Sum.inr (e,j) :=
      (atVertex_eq_inr_iff u v (4*p) e e i.castSucc j).mpr ⟨rfl,by dsimp [j]; omega⟩
    rw [hv]
    have hc := realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e j
      (atVertex u v (4*p) e i.succ)
    have hj : ¬ j.val < 2*p := by dsimp [j]; omega
    have he : j.val+1=i.val := by dsimp [j]; omega
    simpa only [pathActivity,profile_right p (B e) (Hu e) (Hv e) (lam e) i hi,
      internalStrength,ite_eq_right hj,he] using hc

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem realBottleneck_central_edge (w : V → V → ℝ) (p : ℕ) (hp : 1 ≤ p)
    (Hu Hv : LogicalEdge V → ℝ) (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e)
    (hinner : ∀ e, max (bottleneck w (source e) (target e)) (Hu e/2^(p-1)) =
      bottleneck w (source e) (target e)) (e : LogicalEdge V) :
    realBottleneck source target p (fun e => bottleneck w (source e) (target e))
      Hu Hv (logicalActivity w)
      (atVertex source target (4*p) e ⟨2*p,by omega⟩)
      (atVertex source target (4*p) e ⟨2*p+1,by omega⟩) =
      bottleneck w (source e) (target e) := by
  let B := fun e : LogicalEdge V => bottleneck w (source e) (target e)
  let j : Fin (4*p) := ⟨2*p-1,by omega⟩
  let k : Fin (4*p) := ⟨2*p,by omega⟩
  have hj : j.val < 2*p := by dsimp [j]; omega
  have hk : ¬ k.val < 2*p := by simp [k]
  have hjk : j≠k := by intro h; have := congrArg Fin.val h; dsimp [j,k] at this; omega
  have hjv : atVertex source target (4*p) e ⟨2*p,by omega⟩ = Sum.inr (e,j) :=
    (atVertex_eq_inr_iff _ _ _ _ _ _ _).mpr ⟨rfl,by dsimp [j]; omega⟩
  have hkv : atVertex source target (4*p) e ⟨2*p+1,by omega⟩ = Sum.inr (e,k) :=
    (atVertex_eq_inr_iff _ _ _ _ _ _ _).mpr ⟨rfl,rfl⟩
  rw [hjv,hkv]
  have hsj : internalStrength p (B e) (Hu e) (Hv e) j=B e := by
    rw [internalStrength,ite_eq_left hj]
    have hdiv : j.val/2=p-1 := by dsimp [j]; omega
    rw [hdiv]
    exact hinner e
  apply le_antisymm
  · have hc := realBottleneck_internal_cap source target p hp B Hu Hv (logicalActivity w)
        (fun e => one_le_bottleneck w _ _) hHu hHv
        (fun e => edgeActivity_le_bottleneck w _ _ (source_ne_target e)) e j (Sum.inr (e,k))
    exact (hc.trans_eq hsj)
  · let t := activity source target (4*p) (pathActivity p B Hu Hv (logicalActivity w))
    have hleft : B e ≤ bottleneck t (Sum.inr (e,j)) (Sum.inl (source e)) :=
      (le_internalStrength p (B e) (Hu e) (Hv e) j).trans
        (realBottleneck_left_home source target source_ne_target p hp B Hu Hv (logicalActivity w) hHu e j hj)
    have hright : B e ≤ bottleneck t (Sum.inr (e,k)) (Sum.inl (target e)) :=
      (le_internalStrength p (B e) (Hu e) (Hv e) k).trans
        (realBottleneck_right_home source target source_ne_target p hp B Hu Hv (logicalActivity w) hHv e k hk)
    have hterm : bottleneck t (Sum.inl (source e)) (Sum.inl (target e))=B e :=
      terminal_bottleneck w p hp Hu Hv _ _
    have hx : B e ≤ bottleneck t (Sum.inr (e,j)) (Sum.inl (target e)) := by
      have ht := bottleneck_ultrametric t (Sum.inr (e,j)) (Sum.inl (target e)) (Sum.inl (source e))
        (by simp) (by simp) (by simpa using (source_ne_target e).symm)
      exact ((le_min hleft hterm.ge).trans ht)
    have htri := bottleneck_ultrametric t (Sum.inr (e,j)) (Sum.inr (e,k)) (Sum.inl (target e))
      (by simpa using hjk) (by simp) (by simp)
    rw [bottleneck_comm t (Sum.inl (target e)) (Sum.inr (e,k))] at htri
    exact (le_min hx hright).trans htri

theorem source_effective_profile (w : V → V → ℝ) (p : ℕ) (hp : 1≤p)
    (Hu Hv : LogicalEdge V → ℝ) (hHu : ∀ e, 0≤Hu e) (hHv : ∀ e, 0≤Hv e)
    (hinner : ∀ e, max (bottleneck w (source e) (target e)) (Hu e/2^(p-1)) =
      bottleneck w (source e) (target e)) (e : LogicalEdge V) (i : Fin (4*p+1)) :
    realBottleneck source target p (fun e => bottleneck w (source e) (target e)) Hu Hv
      (logicalActivity w) (atVertex source target (4*p) e i.castSucc)
      (atVertex source target (4*p) e i.succ) =
      profileActivity p (bottleneck w (source e) (target e)) (Hu e) (Hv e)
        (bottleneck w (source e) (target e)) i := by
  by_cases hi : i.val=2*p
  · have he : i=⟨2*p,by omega⟩ := Fin.ext hi
    rw [he,profile_center]
    exact realBottleneck_central_edge w p hp Hu Hv hHu hHv hinner e
  · rw [realBottleneck_noncentral_edge source target source_ne_target p hp _ Hu Hv
      (logicalActivity w) (fun _ => one_le_bottleneck _ _ _) hHu hHv
      (fun e => edgeActivity_le_bottleneck w _ _ (source_ne_target e)) e i hi]
    rcases lt_or_gt_of_ne hi with hi | hi
    · simp only [pathActivity,profile_left _ _ _ _ _ _ hi]
    · simp only [pathActivity,profile_right _ _ _ _ _ _ hi]

omit [Fintype V] [LinearOrder V] in
theorem effective_profile_incident_near {E : Type*} (u v : E → V)
    (p : ℕ) (hp : 1≤p) (B : E → ℝ) (H : V → ℝ)
    (hB : ∀ e, 0≤B e) (hH : ∀ x, 0≤H x)
    (hdom : ∀ e, B e≤H (u e) ∧ B e≤H (v e))
    (hinnerL : ∀ e, max (B e) (H (u e)/2^(p-1))=B e)
    (hinnerR : ∀ e, max (B e) (H (v e)/2^(p-1))=B e)
    (x : Vertex V E (4*p)) (e f : E) (i j : Fin (4*p+1))
    (he : x=atVertex u v (4*p) e i.castSucc ∨ x=atVertex u v (4*p) e i.succ)
    (hf : x=atVertex u v (4*p) f j.castSucc ∨ x=atVertex u v (4*p) f j.succ) :
    profileActivity p (B e) (H (u e)) (H (v e)) (B e) i ≤
      2*profileActivity p (B f) (H (u f)) (H (v f)) (B f) j := by
  cases x with
  | inl x =>
    have ht (g : E) (k : Fin (4*p+1))
        (hg : Sum.inl x=atVertex u v (4*p) g k.castSucc ∨ Sum.inl x=atVertex u v (4*p) g k.succ) :
        profileActivity p (B g) (H (u g)) (H (v g)) (B g) k=H x := by
      rcases hg with hg | hg
      · obtain ⟨hk,hx⟩ := (first_vertex_terminal u v (4*p) g k x).mp hg.symm
        rw [profile_left _ _ _ _ _ _ (by omega),hk]
        simp only [Nat.zero_div,pow_zero,div_one,max_eq_right (hdom g).1]
        exact congrArg H hx
      · obtain ⟨hk,hx⟩ := (second_vertex_terminal u v (4*p) g k x).mp hg.symm
        rw [profile_right _ _ _ _ _ _ (by omega),hk]
        simp only [Nat.sub_self,Nat.zero_div,pow_zero,div_one,max_eq_right (hdom g).2]
        exact congrArg H hx
    rw [ht e i he,ht f j hf]
    linarith [hH x]
  | inr z =>
    rcases z with ⟨g,k⟩
    have hi : e=g ∧ (i.val=k.val ∨ i.val=k.val+1) := by
      rcases he with he | he
      · have hh := (atVertex_eq_inr_iff u v (4*p) e g i.castSucc k).mp he.symm
        exact ⟨hh.1,Or.inr hh.2⟩
      · have hh := (atVertex_eq_inr_iff u v (4*p) e g i.succ k).mp he.symm
        exact ⟨hh.1,Or.inl (by simpa using hh.2)⟩
    have hj : f=g ∧ (j.val=k.val ∨ j.val=k.val+1) := by
      rcases hf with hf | hf
      · have hh := (atVertex_eq_inr_iff u v (4*p) f g j.castSucc k).mp hf.symm
        exact ⟨hh.1,Or.inr hh.2⟩
      · have hh := (atVertex_eq_inr_iff u v (4*p) f g j.succ k).mp hf.symm
        exact ⟨hh.1,Or.inl (by simpa using hh.2)⟩
    obtain ⟨rfl,hi⟩ := hi
    obtain ⟨rfl,hj⟩ := hj
    have hnear := profile_adjacent_near p hp (B f) (H (u f)) (H (v f))
      (hB f) (hH _) (hH _) (hinnerL f) (hinnerR f) k
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · have heq : i=j := Fin.ext (hi.trans hj.symm)
      rw [heq]
      have hn := (hB f).trans (profile_lower p (B f) (H (u f)) (H (v f)) (B f) le_rfl j)
      linarith
    · have hi' : i=k.castSucc := Fin.ext hi
      have hj' : j=k.succ := Fin.ext hj
      simpa [hi',hj'] using hnear.1
    · have hi' : i=k.succ := Fin.ext hi
      have hj' : j=k.castSucc := Fin.ext hj
      simpa [hi',hj'] using hnear.2
    · have heq : i=j := Fin.ext (hi.trans hj.symm)
      rw [heq]
      have hn := (hB f).trans (profile_lower p (B f) (H (u f)) (H (v f)) (B f) le_rfl j)
      linarith

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.Hierarchy

theorem acyclic_of_unique_lower {L : Type*} (G : SimpleGraph L) (rank : L → ℕ)
    (hdiff : ∀ {a b}, G.Adj a b → rank a ≠ rank b)
    (hparent : ∀ a b c, G.Adj a b → G.Adj a c → rank b < rank a → rank c < rank a → b=c) :
    G.IsAcyclic := by
  classical
  intro a p hp
  obtain ⟨b,hb,hmax⟩ := p.support.toFinset.exists_max_image rank
    ⟨a,by simp⟩
  have hb' : b ∈ p.support := List.mem_toFinset.mp hb
  let q := p.rotate b hb'
  have hq : q.IsCycle := hp.rotate hb'
  have hqs : q.snd ∈ p.support := (p.mem_support_rotate_iff b hb').mp (q.getVert_mem_support 1)
  have hqt : q.penultimate ∈ p.support :=
    (p.mem_support_rotate_iff b hb').mp (q.getVert_mem_support (q.length-1))
  have hs : rank q.snd < rank b := lt_of_le_of_ne
    (hmax q.snd (List.mem_toFinset.mpr hqs)) (hdiff (q.adj_snd hq.not_nil)).symm
  have ht : rank q.penultimate < rank b := lt_of_le_of_ne
    (hmax q.penultimate (List.mem_toFinset.mpr hqt)) (hdiff (q.adj_penultimate hq.not_nil))
  exact hq.snd_ne_penultimate (hparent b q.snd q.penultimate (q.adj_snd hq.not_nil)
    (q.adj_penultimate hq.not_nil).symm hs ht)

variable {V : Type*} [Fintype V]

variable (B : V → V → ℝ)

variable (hsym : ∀ a b, B a b = B b a)

variable (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)

def Related (t : ℝ) (a b : V) : Prop := a=b ∨ t ≤ B a b

omit [Fintype V] in
include hsym in
lemma related_symm (t : ℝ) {a b : V} (h : Related B t a b) : Related B t b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rwa [hsym])

omit [Fintype V] in
include htri in
lemma related_trans (t : ℝ) {a b c : V} (hab : Related B t a b) (hbc : Related B t b c) :
    Related B t a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  by_cases hac : a=c
  · exact Or.inl hac
  by_cases hab' : a=b
  · subst b; exact Or.inr hbc
  by_cases hbc' : c=b
  · subst c; exact Or.inr hab
  exact Or.inr ((le_min hab hbc).trans (htri a c b hac hab' hbc'))

def thresholdSetoid (t : ℝ) : Setoid V where
  r := Related B t
  iseqv := ⟨fun _ => Or.inl rfl,related_symm B hsym t,related_trans B htri t⟩

abbrev Component (t : ℝ) := Quotient (thresholdSetoid B hsym htri t)

abbrev Label (H : ℕ) := (k : Fin (H+1)) × Component B hsym htri (2^k.val)

def labelAt {H : ℕ} (k : Fin (H+1)) (x : V) : Label B hsym htri H :=
  ⟨k,Quotient.mk _ x⟩

def Mem {H : ℕ} (l : Label B hsym htri H) (x : V) : Prop := Quotient.mk _ x = l.2

omit [Fintype V] in
lemma mem_labelAt {H : ℕ} (k : Fin (H+1)) (x : V) : Mem B hsym htri (labelAt B hsym htri k x) x := rfl

omit [Fintype V] in
lemma mem_class_iff {H : ℕ} (k : Fin (H+1)) (x y : V) :
    Mem B hsym htri (labelAt B hsym htri k x) y ↔ Related B (2^k.val) y x :=
  Quotient.eq

omit [Fintype V] in
lemma exists_mem {H : ℕ} (l : Label B hsym htri H) : ∃ x, Mem B hsym htri l x :=
  Quotient.exists_rep l.2

omit [Fintype V] in
lemma eq_of_level_of_mem {H : ℕ} (a b : Label B hsym htri H) (hlev : a.1=b.1)
    {x : V} (ha : Mem B hsym htri a x) (hb : Mem B hsym htri b x) : a=b := by
  cases a with
  | mk k a =>
    cases b with
    | mk j b =>
      dsimp at hlev
      subst j
      exact congrArg (Sigma.mk k) (ha.symm.trans hb)

omit [Fintype V] in
lemma related_of_mem {H : ℕ} (l : Label B hsym htri H) {x y : V}
    (hx : Mem B hsym htri l x) (hy : Mem B hsym htri l y) : Related B (2^l.1.val) x y :=
  Quotient.exact (hx.trans hy.symm)

omit [Fintype V] in
lemma mem_of_related {H : ℕ} (l : Label B hsym htri H) {x y : V}
    (hx : Mem B hsym htri l x) (hxy : Related B (2^l.1.val) y x) : Mem B hsym htri l y :=
  (Quotient.sound hxy).trans hx

omit [Fintype V] in
lemma related_mono {s t : ℝ} (hst : s ≤ t) {a b : V} (h : Related B t a b) :
    Related B s a b := h.imp id (fun hb => hst.trans hb)

def Parent {H : ℕ} (a b : Label B hsym htri H) : Prop :=
  a.1.val+1=b.1.val ∧ ∃ x, Mem B hsym htri a x ∧ Mem B hsym htri b x

def tree {H : ℕ} : SimpleGraph (Label B hsym htri H) where
  Adj a b := Parent B hsym htri a b ∨ Parent B hsym htri b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro a h; rcases h with h|h <;> have := h.1 <;> omega⟩

omit [Fintype V] in
lemma parent_mem {H : ℕ} {a b : Label B hsym htri H} (h : Parent B hsym htri a b)
    {x : V} (hx : Mem B hsym htri b x) : Mem B hsym htri a x := by
  obtain ⟨hlev,y,hy,hby⟩ := h
  have hpow : (2:ℝ)^a.1.val ≤ 2^b.1.val := pow_le_pow_right₀ (by norm_num) (by omega)
  exact mem_of_related B hsym htri a hy
    (related_mono B hpow (related_of_mem B hsym htri b hx hby))

omit [Fintype V] in
lemma parent_unique {H : ℕ} {a b c : Label B hsym htri H}
    (ha : Parent B hsym htri a c) (hb : Parent B hsym htri b c) : a=b := by
  obtain ⟨x,hx⟩ := exists_mem B hsym htri c
  apply eq_of_level_of_mem B hsym htri a b _
    (parent_mem B hsym htri ha hx) (parent_mem B hsym htri hb hx)
  apply Fin.ext
  have := ha.1
  have := hb.1
  omega

omit [Fintype V] in
theorem tree_acyclic (H : ℕ) : (tree B hsym htri (H := H)).IsAcyclic := by
  apply acyclic_of_unique_lower _ (fun l => l.1.val)
  · intro a b hab
    rcases hab with h | h <;> have := h.1 <;> omega
  · intro a b c hab hac hb hc
    have hp : Parent B hsym htri b a := by
      rcases hab with h | h
      · have := h.1; omega
      · exact h
    have hq : Parent B hsym htri c a := by
      rcases hac with h | h
      · have := h.1; omega
      · exact h
    exact parent_unique B hsym htri hp hq

omit [Fintype V] in
lemma parent_exists {H : ℕ} (a : Label B hsym htri H) (ha : 0<a.1.val) :
    ∃ b, Parent B hsym htri b a := by
  obtain ⟨x,hx⟩ := exists_mem B hsym htri a
  let k : Fin (H+1) := ⟨a.1.val-1,by have := a.1.isLt; omega⟩
  exact ⟨labelAt B hsym htri k x,by dsimp [Parent,k,labelAt]; exact ⟨by omega,x,rfl,hx⟩⟩

variable (hfloor : ∀ a b, 1 ≤ B a b)

omit [Fintype V] in
include hfloor in
lemma level_zero_unique {H : ℕ} (a b : Label B hsym htri H)
    (ha : a.1.val=0) (hb : b.1.val=0) : a=b := by
  obtain ⟨x,hx⟩ := exists_mem B hsym htri a
  obtain ⟨y,hy⟩ := exists_mem B hsym htri b
  apply eq_of_level_of_mem B hsym htri a b (Fin.ext (ha.trans hb.symm)) hx
  apply mem_of_related B hsym htri b hy
  exact Or.inr (by simpa [hb] using hfloor x y)

omit [Fintype V] in
lemma reaches_level_zero {H : ℕ} (a : Label B hsym htri H) :
    ∃ b, b.1.val=0 ∧ (tree B hsym htri).Reachable a b := by
  induction h : a.1.val using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n=0
    · exact ⟨a,h.trans hn,SimpleGraph.Reachable.refl a⟩
    · obtain ⟨b,hb⟩ := parent_exists B hsym htri a (by omega)
      obtain ⟨c,hc,hbc⟩ := ih b.1.val (by have := hb.1; omega) b rfl
      exact ⟨c,hc,(SimpleGraph.Adj.reachable (show (tree B hsym htri).Adj a b from Or.inr hb)).trans hbc⟩

omit [Fintype V] in
include hfloor in
theorem tree_connected [Nonempty V] (H : ℕ) : (tree B hsym htri (H := H)).Connected := by
  classical
  let : Nonempty (Label B hsym htri H) := ⟨labelAt B hsym htri 0 (Classical.choice inferInstance)⟩
  refine ⟨?_⟩
  intro a b
  obtain ⟨a₀,ha₀,ha⟩ := reaches_level_zero B hsym htri a
  obtain ⟨b₀,hb₀,hb⟩ := reaches_level_zero B hsym htri b
  have he := level_zero_unique B hsym htri hfloor a₀ b₀ ha₀ hb₀
  subst b₀
  exact ha.trans hb.symm

noncomputable instance labelFintype (H : ℕ) : Fintype (Label B hsym htri H) := Fintype.ofFinite _

theorem label_card_le (H : ℕ) : Fintype.card (Label B hsym htri H) ≤ (H+1)*Fintype.card V := by
  classical
  have hs : Function.Surjective (fun z : Fin (H+1) × V => labelAt B hsym htri z.1 z.2) := by
    intro a
    obtain ⟨x,hx⟩ := exists_mem B hsym htri a
    exact ⟨(a.1,x),Sigma.ext rfl (heq_of_eq hx)⟩
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_surjective _ hs

noncomputable def dyadicLevel (H : ℕ) (x : ℝ) : Fin (H+1) := by
  classical
  exact ⟨Nat.findGreatest (fun k => (2:ℝ)^k ≤ x) H,
    Nat.lt_succ_of_le (Nat.findGreatest_le H)⟩

lemma dyadic_lower (H : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    (2:ℝ)^(dyadicLevel H x).val ≤ x := by
  classical
  exact Nat.findGreatest_spec (P := fun k => (2:ℝ)^k ≤ x) (Nat.zero_le H) (by simpa using hx)

lemma dyadic_upper (H : ℕ) (x : ℝ) (hx : x ≤ (2:ℝ)^H) :
    x < (2:ℝ)^((dyadicLevel H x).val+1) := by
  classical
  by_cases he : (dyadicLevel H x).val=H
  · rw [he,pow_succ]
    have : 0 < (2:ℝ)^H := by positivity
    linarith
  · by_contra hn
    have hle : (dyadicLevel H x).val+1 ≤ H := by have := (dyadicLevel H x).isLt; omega
    have hg := Nat.le_findGreatest (P := fun k => (2:ℝ)^k ≤ x) hle (le_of_not_gt hn)
    change (dyadicLevel H x).val+1 ≤ (dyadicLevel H x).val at hg
    omega

lemma dyadic_near (H : ℕ) (x y : ℝ) (hxlo : 1 ≤ x) (hyhi : y ≤ (2:ℝ)^H)
    (hxy : x ≤ 2*y) : (dyadicLevel H x).val ≤ (dyadicLevel H y).val+1 := by
  by_contra hn
  have hpow : (2:ℝ)^((dyadicLevel H y).val+2) ≤ 2^(dyadicLevel H x).val :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hx := dyadic_lower H x hxlo
  have hy := dyadic_upper H y hyhi
  rw [show (dyadicLevel H y).val+2=((dyadicLevel H y).val+1)+1 by omega,pow_succ] at hpow
  linarith

lemma dyadic_upper_of_lt (H : ℕ) (x : ℝ) (hx : x < (2:ℝ)^(H+1)) :
    x < (2:ℝ)^((dyadicLevel H x).val+1) := by
  classical
  by_cases he : (dyadicLevel H x).val=H
  · simpa [he] using hx
  · by_contra hn
    have hle : (dyadicLevel H x).val+1 ≤ H := by have := (dyadicLevel H x).isLt; omega
    have hg := Nat.le_findGreatest (P := fun k => (2:ℝ)^k ≤ x) hle (le_of_not_gt hn)
    change (dyadicLevel H x).val+1 ≤ (dyadicLevel H x).val at hg
    omega

lemma dyadic_near_of_lt (H : ℕ) (x y : ℝ) (hxlo : 1≤x) (hyhi : y < (2:ℝ)^(H+1))
    (hxy : x≤2*y) : (dyadicLevel H x).val ≤ (dyadicLevel H y).val+1 := by
  by_contra hn
  have hpow : (2:ℝ)^((dyadicLevel H y).val+2) ≤ 2^(dyadicLevel H x).val :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hx := dyadic_lower H x hxlo
  have hy := dyadic_upper_of_lt H y hyhi
  rw [show (dyadicLevel H y).val+2=((dyadicLevel H y).val+1)+1 by omega,pow_succ] at hpow
  linarith

omit [Fintype V] in
lemma common_vertex_adjacent {H : ℕ} (a b : Label B hsym htri H) {x : V}
    (ha : Mem B hsym htri a x) (hb : Mem B hsym htri b x)
    (hab : a.1.val ≤ b.1.val+1) (hba : b.1.val ≤ a.1.val+1) :
    a=b ∨ (tree B hsym htri).Adj a b := by
  rcases lt_trichotomy a.1.val b.1.val with h | h | h
  · exact Or.inr (Or.inl ⟨by omega,x,ha,hb⟩)
  · exact Or.inl (eq_of_level_of_mem B hsym htri a b (Fin.ext h) ha hb)
  · exact Or.inr (Or.inr ⟨by omega,x,hb,ha⟩)

omit [Fintype V] in
lemma memberships_card_le_two {H : ℕ} (S : Finset (Label B hsym htri H)) (x : V)
    (hmem : ∀ a ∈ S, Mem B hsym htri a x)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a.1.val ≤ b.1.val+1) : S.card ≤ 2 := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨a,ha,hmin⟩ := S.exists_min_image (fun a => a.1.val) hne
    have hinj : Set.InjOn (fun a : Label B hsym htri H => a.1.val) S := by
      intro b hb c hc he
      exact eq_of_level_of_mem B hsym htri b c (Fin.ext he) (hmem b hb) (hmem c hc)
    have hsub : S.image (fun a => a.1.val) ⊆ {a.1.val,a.1.val+1} := by
      intro k hk
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hk
      have h₁ := hmin b hb
      have h₂ := hsep b hb a ha
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    calc
      S.card = (S.image (fun a => a.1.val)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ({a.1.val,a.1.val+1} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := by simp
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

variable {E : Type*} [Fintype E] (left right : E → V) (H : ℕ)

def Incident (e : E) (x : V) : Prop := x=left e ∨ x=right e

noncomputable def edgeLabel (e : E) : Label B hsym htri H :=
  labelAt B hsym htri (dyadicLevel H (B (left e) (right e))) (left e)

noncomputable def memberships (x : V) : Finset (Label B hsym htri H) := by
  classical
  exact (Finset.univ.filter (fun e => Incident left right e x)).image
    (edgeLabel B hsym htri left right H)

omit [Fintype V] in
lemma mem_memberships (x : V) (l : Label B hsym htri H) :
    l ∈ memberships B hsym htri left right H x ↔
      ∃ e, Incident left right e x ∧ edgeLabel B hsym htri left right H e=l := by
  classical
  simp [memberships]

omit [Fintype V] [Fintype E] in
include hfloor in
lemma incident_mem_label (e : E) {x : V} (hx : Incident left right e x) :
    Mem B hsym htri (edgeLabel B hsym htri left right H e) x := by
  rcases hx with rfl | rfl
  · rfl
  · apply (mem_class_iff B hsym htri _ _ _).mpr
    exact Or.inr (by rw [hsym]; exact dyadic_lower H _ (hfloor _ _))

omit [Fintype V] in
include hfloor in
lemma membership_mem {x : V} {l : Label B hsym htri H}
    (hl : l ∈ memberships B hsym htri left right H x) : Mem B hsym htri l x := by
  obtain ⟨e,he,rfl⟩ := (mem_memberships B hsym htri left right H x l).mp hl
  exact incident_mem_label B hsym htri hfloor left right H e he

variable (hupper : ∀ e, B (left e) (right e) < (2:ℝ)^(H+1))

variable (hnear : ∀ x e f, Incident left right e x → Incident left right f x →
  B (left e) (right e) ≤ 2*B (left f) (right f))

omit [Fintype V] in
include hfloor hupper hnear in
lemma memberships_level_near {x : V} {a b : Label B hsym htri H}
    (ha : a ∈ memberships B hsym htri left right H x)
    (hb : b ∈ memberships B hsym htri left right H x) : a.1.val ≤ b.1.val+1 := by
  obtain ⟨e,he,rfl⟩ := (mem_memberships B hsym htri left right H x a).mp ha
  obtain ⟨f,hf,rfl⟩ := (mem_memberships B hsym htri left right H x b).mp hb
  exact dyadic_near_of_lt H _ _ (hfloor _ _) (hupper f) (hnear x e f he hf)

omit [Fintype V] in
include hfloor hupper hnear in

theorem memberships_tree_bags (x : V) (a b : Label B hsym htri H)
    (ha : a ∈ memberships B hsym htri left right H x)
    (hb : b ∈ memberships B hsym htri left right H x) :
    a=b ∨ (tree B hsym htri).Adj a b := by
  exact common_vertex_adjacent B hsym htri a b
    (membership_mem B hsym htri hfloor left right H ha)
    (membership_mem B hsym htri hfloor left right H hb)
    (memberships_level_near B hsym htri hfloor left right H hupper hnear ha hb)
    (memberships_level_near B hsym htri hfloor left right H hupper hnear hb ha)

omit [Fintype V] in
include hfloor hupper hnear in
lemma membership_count (x : V) : (memberships B hsym htri left right H x).card ≤ 2 := by
  apply memberships_card_le_two B hsym htri _ x
  · intro a ha; exact membership_mem B hsym htri hfloor left right H ha
  · intro a ha b hb
    exact memberships_level_near B hsym htri hfloor left right H hupper hnear ha hb

omit [Fintype V] in
include hfloor in
lemma common_height_le {x y : V} {l : Label B hsym htri H} (hxy : x≠y)
    (hx : l ∈ memberships B hsym htri left right H x)
    (hy : l ∈ memberships B hsym htri left right H y) : (2:ℝ)^l.1.val ≤ B x y := by
  exact (related_of_mem B hsym htri l
    (membership_mem B hsym htri hfloor left right H hx)
    (membership_mem B hsym htri hfloor left right H hy)).resolve_left hxy

omit [Fintype V] [Fintype E] in
include hupper in
lemma edge_strength_lt_twice_height (e : E) :
    B (left e) (right e) < 2*(2:ℝ)^(edgeLabel B hsym htri left right H e).1.val := by
  simpa [edgeLabel,labelAt,pow_succ,mul_comm] using dyadic_upper_of_lt H _ (hupper e)

omit [Fintype V] in
lemma adjacent_heights {a b : Label B hsym htri H} (hab : (tree B hsym htri).Adj a b) :
    (2:ℝ)^a.1.val ≤ 2*(2:ℝ)^b.1.val ∧ (2:ℝ)^b.1.val ≤ 2*(2:ℝ)^a.1.val := by
  rcases hab with h | h <;> have he := h.1
  · have hpow : (2:ℝ)^b.1.val=2*2^a.1.val := by rw [←he,pow_succ]; ring
    rw [hpow]; constructor <;> nlinarith [pow_pos (by norm_num : (0:ℝ)<2) a.1.val]
  · have hpow : (2:ℝ)^a.1.val=2*2^b.1.val := by rw [←he,pow_succ]; ring
    rw [hpow]; constructor <;> nlinarith [pow_pos (by norm_num : (0:ℝ)<2) b.1.val]

end MatchingFPRAS.Hierarchy

end OAI
