import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

namespace Problem336

theorem rawPair_comm (u v : ℕ) : rawPair u v = rawPair v u := by
  unfold rawPair
  split_ifs <;> simp_all <;> omega

@[simp] theorem rawPair_of_lt {u v : ℕ} (h : u < v) :
    rawPair u v = (u, v) := by
  simp [rawPair, h]

@[simp] theorem mkEdge_val (u v : ℕ) (h : u ≠ v) :
    (mkEdge u v h).val = rawPair u v := by
  unfold mkEdge rawPair
  split_ifs <;> rfl

@[simp] theorem mkEdge_of_lt {u v : ℕ} (h : u < v) :
    mkEdge u v (Nat.ne_of_lt h) = ⟨(u, v), h⟩ := by
  simp [mkEdge, h]

theorem mkEdge_swap (u v : ℕ) (h : u ≠ v) :
    mkEdge u v h = mkEdge v u h.symm := by
  apply Subtype.ext
  simpa only [mkEdge_val] using rawPair_comm u v

@[simp] theorem mkEdge_endpoints (e : EdgeCode) :
    mkEdge e.val.1 e.val.2 (Nat.ne_of_lt e.property) = e := by
  apply Subtype.ext
  simp [mkEdge, e.property]

theorem mapEdge_mkEdge (σ : Equiv ℕ ℕ) (u v : ℕ) (h : u ≠ v) :
    mapEdge σ (mkEdge u v h) =
      mkEdge (σ u) (σ v) (fun huv => h (σ.injective huv)) := by
  by_cases huv : u < v
  · simp [mapEdge, mkEdge, huv]
  · have hvu : v < u := lt_of_le_of_ne (Nat.le_of_not_gt huv) h.symm
    have he : mkEdge u v h = ⟨(v, u), hvu⟩ := by
      simp [mkEdge, huv]
    rw [he]
    change mkEdge (σ v) (σ u) _ = mkEdge (σ u) (σ v) _
    exact mkEdge_swap _ _ _

@[simp] theorem mapEdge_refl (e : EdgeCode) :
    mapEdge (Equiv.refl ℕ) e = e := by
  change mkEdge e.val.1 e.val.2 _ = e
  exact mkEdge_endpoints e

theorem mapEdge_trans (σ τ : Equiv ℕ ℕ) (e : EdgeCode) :
    mapEdge (σ.trans τ) e = mapEdge τ (mapEdge σ e) := by
  symm
  exact mapEdge_mkEdge τ (σ e.val.1) (σ e.val.2) _

@[simp] theorem mapEdge_symm_apply (σ : Equiv ℕ ℕ) (e : EdgeCode) :
    mapEdge σ.symm (mapEdge σ e) = e := by
  rw [← mapEdge_trans]
  simp

@[simp] theorem mapEdge_apply_symm (σ : Equiv ℕ ℕ) (e : EdgeCode) :
    mapEdge σ (mapEdge σ.symm e) = e := by
  simpa using mapEdge_symm_apply σ.symm e

def edgeEquiv (σ : Equiv ℕ ℕ) : Equiv EdgeCode EdgeCode where
  toFun := mapEdge σ
  invFun := mapEdge σ.symm
  left_inv := mapEdge_symm_apply σ
  right_inv := mapEdge_apply_symm σ

@[simp] theorem edgeEquiv_apply (σ : Equiv ℕ ℕ) (e : EdgeCode) :
    edgeEquiv σ e = mapEdge σ e := rfl

theorem mapEdge_injective (σ : Equiv ℕ ℕ) : Function.Injective (mapEdge σ) :=
  (edgeEquiv σ).injective

theorem mapEdge_surjective (σ : Equiv ℕ ℕ) : Function.Surjective (mapEdge σ) :=
  (edgeEquiv σ).surjective

@[simp] theorem mapEdge_inj (σ : Equiv ℕ ℕ) (e f : EdgeCode) :
    mapEdge σ e = mapEdge σ f ↔ e = f := (mapEdge_injective σ).eq_iff

end Problem336

end

end OAI
