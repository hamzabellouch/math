import OAI.Combinatorics.HalvingLines.CrossingEstimate

namespace OAI

open Filter Topology

namespace PlanarHalving
namespace Batches

variable {α : Type*} [DecidableEq α]

noncomputable def transport (M M' : Finset α) (e : ↥(M \ M') ≃ ↥(M' \ M)) :
    ↥M ≃ ↥M' where
  toFun u := if h : (u : α) ∈ M' then ⟨u, h⟩
    else let v := e ⟨u, Finset.mem_sdiff.mpr ⟨u.property, h⟩⟩
         ⟨v.val, (Finset.mem_sdiff.mp v.property).1⟩
  invFun v := if h : (v : α) ∈ M then ⟨v, h⟩
    else let u := e.symm ⟨v, Finset.mem_sdiff.mpr ⟨v.property, h⟩⟩
         ⟨u.val, (Finset.mem_sdiff.mp u.property).1⟩
  left_inv := by
    intro u
    by_cases h : (u : α) ∈ M'
    · simp only [h, u.property, ↓reduceDIte]
    · have hn := (Finset.mem_sdiff.mp (e ⟨u.val,
        Finset.mem_sdiff.mpr ⟨u.property, h⟩⟩).property).2
      simp only [h, hn, ↓reduceDIte]
      exact congrArg (fun w : ↥(M \ M') => (⟨w.val,
        (Finset.mem_sdiff.mp w.property).1⟩ : ↥M)) (e.symm_apply_apply _)
  right_inv := by
    intro v
    by_cases h : (v : α) ∈ M
    · simp only [h, v.property, ↓reduceDIte]
    · have hn := (Finset.mem_sdiff.mp (e.symm ⟨v.val,
        Finset.mem_sdiff.mpr ⟨v.property, h⟩⟩).property).2
      simp only [h, hn, ↓reduceDIte]
      exact congrArg (fun w : ↥(M' \ M) => (⟨w.val,
        (Finset.mem_sdiff.mp w.property).1⟩ : ↥M')) (e.apply_symm_apply _)

lemma transport_of_mem {M M' : Finset α} (e : ↥(M \ M') ≃ ↥(M' \ M))
    (u : ↥M) (hu : (u : α) ∈ M') : (transport M M' e u : α) = u := by
  simp [transport, hu]

lemma transport_of_not_mem {M M' : Finset α} (e : ↥(M \ M') ≃ ↥(M' \ M))
    (u : ↥M) (hu : (u : α) ∉ M') :
    (transport M M' e u : α) = (e ⟨u.val, Finset.mem_sdiff.mpr ⟨u.property, hu⟩⟩ : α) := by
  simp [transport, hu]

noncomputable def matching {a : ℕ} [NeZero a] {L G : Type*}
    (l : L ≃ Fin a) (g : G ≃ Fin a) (j : Fin a) : L ≃ G :=
  l.trans ((Equiv.addRight j).trans g.symm)

lemma matching_unique {a : ℕ} [NeZero a] {L G : Type*}
    (l : L ≃ Fin a) (g : G ≃ Fin a) (u : L) (v : G) :
    ∃! j, matching l g j u = v := by
  refine ⟨g v - l u, ?_, ?_⟩
  · apply g.injective
    simp [matching]
  · intro j hj
    have h : l u + j = g v := by
      simpa [matching] using congrArg g hj
    exact eq_sub_of_add_eq' h

structure System {n R k a : ℕ} (P : Fin n → Point) where
  slope : Fin (R + 1) → ℝ
  increasing : StrictMono slope
  marks : Fin (R + 1) → Finset (Fin n)
  card_marks : ∀ b, (marks b).card = k
  separates : ∀ b, Sweep.Separates P (slope b) (marks b)
  distance : ∀ b : Fin R, (marks b.castSucc \ marks b.succ).card = a

variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.loss (S : @System n R k a P) (b : Fin R) : Finset (Fin n) :=
  S.marks b.castSucc \ S.marks b.succ
noncomputable def System.gain (S : @System n R k a P) (b : Fin R) : Finset (Fin n) :=
  S.marks b.succ \ S.marks b.castSucc

lemma System.card_loss (S : @System n R k a P) (b : Fin R) : (S.loss b).card = a :=
  S.distance b
lemma System.card_gain (S : @System n R k a P) (b : Fin R) : (S.gain b).card = a := by
  rw [System.gain, Finset.card_sdiff_comm (by rw [S.card_marks, S.card_marks])]
  exact S.card_loss b

noncomputable def System.lossIndex (S : @System n R k a P) (b : Fin R) : ↥(S.loss b) ≃ Fin a :=
  Fintype.equivFinOfCardEq (by simpa using S.card_loss b)
noncomputable def System.gainIndex (S : @System n R k a P) (b : Fin R) : ↥(S.gain b) ≃ Fin a :=
  Fintype.equivFinOfCardEq (by simpa using S.card_gain b)

noncomputable def System.match (S : @System n R k a P) [NeZero a] (j : Fin a) (b : Fin R) :
    ↥(S.loss b) ≃ ↥(S.gain b) := matching (S.lossIndex b) (S.gainIndex b) j

noncomputable def System.transition (S : @System n R k a P) [NeZero a]
    (j : Fin a) (b : Fin R) : ↥(S.marks b.castSucc) ≃ ↥(S.marks b.succ) :=
  transport _ _ (S.match j b)

noncomputable def System.tokenState (S : @System n R k a P) [NeZero a]
    (j : Fin a) (b : Fin (R + 1)) : ↥(S.marks 0) ≃ ↥(S.marks b) :=
  Fin.induction (Equiv.refl _) (fun b e => e.trans (S.transition j b)) b

@[simp] lemma System.tokenState_zero (S : @System n R k a P) [NeZero a]
    (j : Fin a) : S.tokenState j 0 = Equiv.refl _ := by simp [System.tokenState]

lemma System.tokenState_succ (S : @System n R k a P) [NeZero a]
    (j : Fin a) (b : Fin R) (u : ↥(S.marks 0)) :
    S.tokenState j b.succ u = S.transition j b (S.tokenState j b.castSucc u) := by
  simp [System.tokenState, Fin.induction_succ]

lemma System.edge_right (S : @System n R k a P) (b : Fin R)
    {u v : Fin n} (hu : u ∈ S.loss b) (hv : v ∈ S.gain b) : (P u).1 < (P v).1 := by
  exact Sweep.exchange_rightward (S.increasing (Fin.castSucc_lt_succ (i := b))).le
    (S.separates b.castSucc) (S.separates b.succ) hu hv

lemma System.edge_slope (S : @System n R k a P) (b : Fin R)
    {u v : Fin n} (hu : u ∈ S.loss b) (hv : v ∈ S.gain b) :
    S.slope b.castSucc < PlanarHalving.slope (P u) (P v) ∧
    PlanarHalving.slope (P u) (P v) < S.slope b.succ :=
  Sweep.exchange_slope_between (S.increasing (Fin.castSucc_lt_succ (i := b))).le
    (S.separates b.castSucc) (S.separates b.succ) hu hv

end Batches
end PlanarHalving

namespace PlanarHalving.Batches
open PlaneGraph

lemma fin_between_le {R : ℕ} {f : Fin (R + 1) → ℝ} (i j : Fin (R + 1))
    (hij : i ≤ j)
    (hstep : ∀ r : Fin R, i ≤ r.castSucc → r.succ ≤ j → f r.castSucc ≤ f r.succ) :
    f i ≤ f j := by
  induction j using Fin.induction with
  | zero =>
    have hi : i = 0 := Fin.ext (by simpa using hij)
    subst i
    exact le_rfl
  | succ r ih =>
    by_cases hi : i ≤ r.castSucc
    · exact (ih hi (fun s hs ht => hstep s hs (ht.trans (Fin.castSucc_le_succ r)))).trans
        (hstep r hi le_rfl)
    · have he : i = r.succ := Fin.ext (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at *; omega)
      subst i
      exact le_rfl

structure ConvexPath (R : ℕ) where
  point : Fin (R + 1) → Point
  right : ∀ r : Fin R, point r.castSucc = point r.succ ∨
    (point r.castSucc).1 < (point r.succ).1
  slopes : ∀ r s : Fin R, r < s → point r.castSucc ≠ point r.succ →
    point s.castSucc ≠ point s.succ →
    slope (point r.castSucc) (point r.succ) ≤ slope (point s.castSucc) (point s.succ)

lemma projection_step (p q : Point) {t : ℝ} (hx : p.1 ≠ q.1) :
    Sweep.projection t q - Sweep.projection t p =
      (q.1 - p.1) * (slope p q - t) := by
  unfold Sweep.projection slope
  field_simp
  ring

variable {R : ℕ}

lemma ConvexPath.x_mono (C : ConvexPath R) : Monotone (fun r => (C.point r).1) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro r
  rcases C.right r with h | h
  · exact le_of_eq (congrArg Prod.fst h)
  · exact h.le

lemma ConvexPath.support_vertex (C : ConvexPath R) (b : Fin R)
    (hb : C.point b.castSucc ≠ C.point b.succ) (c : Fin (R + 1)) :
    height (C.point b.castSucc) (C.point b.succ) (C.point c).1 ≤ (C.point c).2 := by
  let t := slope (C.point b.castSucc) (C.point b.succ)
  have hb' := (C.right b).resolve_left hb
  have hroot : Sweep.projection t (C.point b.castSucc) =
      Sweep.projection t (C.point b.succ) := by
    have hh := projection_step (C.point b.castSucc) (C.point b.succ) (t := t) hb'.ne
    simp only [t, sub_self, mul_zero] at hh
    linarith
  have hmin : Sweep.projection t (C.point b.castSucc) ≤ Sweep.projection t (C.point c) := by
    by_cases hc : c ≤ b.castSucc
    · have hh := fin_between_le (f := fun r => -Sweep.projection t (C.point r)) c b.castSucc hc
      apply neg_le_neg_iff.mp
      apply hh
      intro r _ hr
      rcases C.right r with he | hx
      · rw [he]
      · have hne : C.point r.castSucc ≠ C.point r.succ := fun he => hx.ne (congrArg Prod.fst he)
        have hlt : r < b := by simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *; omega
        have hs := C.slopes r b hlt hne hb
        have hd := projection_step (C.point r.castSucc) (C.point r.succ) (t := t) hx.ne
        have hn := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.le) (sub_nonpos.mpr hs)
        dsimp only [t] at hd ⊢
        linarith only [hd, hn]
    · have hc' : b.succ ≤ c := by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at *; omega
      rw [hroot]
      apply fin_between_le (f := fun r => Sweep.projection t (C.point r)) b.succ c hc'
      intro r hr _
      rcases C.right r with he | hx
      · rw [he]
      · have hne : C.point r.castSucc ≠ C.point r.succ := fun he => hx.ne (congrArg Prod.fst he)
        have hlt : b < r := by simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *; omega
        have hs := C.slopes b r hlt hb hne
        have hd := projection_step (C.point r.castSucc) (C.point r.succ) (t := t) hx.ne
        have hn := mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hs)
        change Sweep.projection t (C.point r.castSucc) ≤ Sweep.projection t (C.point r.succ)
        dsimp only [t] at hd ⊢
        linarith only [hd, hn]
  unfold Sweep.projection at hmin
  unfold height
  dsimp only [t] at hmin
  linarith only [hmin]

lemma ConvexPath.support_segment (C : ConvexPath R) (b : Fin R)
    (hb : C.point b.castSucc ≠ C.point b.succ) (c : Fin R) {z : Point}
    (hz : z ∈ segment ℝ (C.point c.castSucc) (C.point c.succ)) :
    height (C.point b.castSucc) (C.point b.succ) z.1 ≤ z.2 := by
  rw [segment_eq_image] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  have h₀ := C.support_vertex b hb c.castSucc
  have h₁ := C.support_vertex b hb c.succ
  have hw₀ := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr h₀)
  have hw₁ := mul_nonneg hu.1 (sub_nonneg.mpr h₁)
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, height] at *
  nlinarith only [hw₀, hw₁]

variable {n k a : ℕ} {P : Fin n → Point}

lemma System.token_step (S : @System n R k a P) [NeZero a]
    (j : Fin a) (u : ↥(S.marks 0)) (b : Fin R) :
    (S.tokenState j b.castSucc u : Fin n) = (S.tokenState j b.succ u : Fin n) ∨
      (S.tokenState j b.castSucc u : Fin n) ∈ S.loss b ∧
      (S.tokenState j b.succ u : Fin n) ∈ S.gain b := by
  rw [S.tokenState_succ]
  by_cases h : (S.tokenState j b.castSucc u : Fin n) ∈ S.marks b.succ
  · left
    exact (transport_of_mem (S.match j b) _ h).symm
  · right
    refine ⟨Finset.mem_sdiff.mpr ⟨(S.tokenState j b.castSucc u).property, h⟩, ?_⟩
    change (transport _ _ (S.match j b) _ : Fin n) ∈ _
    rw [transport_of_not_mem (S.match j b) _ h]
    exact (S.match j b ⟨_, Finset.mem_sdiff.mpr ⟨(S.tokenState j b.castSucc u).property, h⟩⟩).property

noncomputable def System.tokenPath (S : @System n R k a P) [NeZero a]
    (j : Fin a) (u : ↥(S.marks 0)) : ConvexPath R where
  point b := P (S.tokenState j b u)
  right b := by
    rcases S.token_step j u b with h | ⟨h₀,h₁⟩
    · exact Or.inl (congrArg P h)
    · exact Or.inr (S.edge_right b h₀ h₁)
  slopes b c hbc hb hc := by
    have hb' := (S.token_step j u b).resolve_left (fun h => hb (congrArg P h))
    have hc' := (S.token_step j u c).resolve_left (fun h => hc (congrArg P h))
    have hs₁ := S.edge_slope b hb'.1 hb'.2
    have hs₂ := S.edge_slope c hc'.1 hc'.2
    have horder : b.succ ≤ c.castSucc := by
      simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *
      omega
    exact (hs₁.2.trans_le (S.increasing.monotone horder)).trans hs₂.1 |>.le

end PlanarHalving.Batches

end OAI
