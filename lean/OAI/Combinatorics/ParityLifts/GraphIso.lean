import OAI.Combinatorics.ParityLifts.SATChoice

namespace OAI

namespace ParityWL

lemma finite_histogram_equiv {α β γ : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → γ) (g : β → γ) (h : ∀ a, f a = g (e a)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  calc
    _ = Finset.univ.val.map (g ∘ e) := by congr 1; funext a; exact h a
    _ = (Finset.univ.val.map e).map g := (Multiset.map_map _ _ _).symm
    _ = _ := by rw [Multiset.map_univ_val_equiv]

lemma iso_atomicType {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : G ≃g H) (k : ℕ) (x : Fin k → V) : atomicType G x = atomicType H (e ∘ x) := by
  classical
  funext i j
  simp [atomicType, e.injective.eq_iff, e.map_adj_iff]

lemma iso_update {V W : Type} (f : V → W) (k : ℕ) (x : Fin k → V) (i : Fin k) (v : V) :
    f ∘ Function.update x i v = Function.update (f ∘ x) i (f v) := by
  classical
  funext j
  by_cases h : j=i <;> simp [h]

lemma iso_jointColor {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) (k r : ℕ) (x : Fin k → V) :
    jointColor G k r x = jointColor H k r (e ∘ x) := by
  induction r generalizing x with
  | zero => exact iso_atomicType G H e k x
  | succ r ih =>
    change (_,_) = (_,_)
    congr 1
    · exact ih x
    · apply finite_histogram_equiv e.toEquiv
      intro v
      funext i
      rw [ih, iso_update]
      rfl

lemma iso_separateColor {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) (k r : ℕ) (x : Fin k → V) :
    separateColor G k r x = separateColor H k r (e ∘ x) := by
  induction r generalizing x with
  | zero => exact iso_atomicType G H e k x
  | succ r ih =>
    change (_,_) = (_,_)
    congr 1
    · exact ih x
    · funext i
      apply finite_histogram_equiv e.toEquiv
      intro v
      rw [ih, iso_update]
      rfl

lemma iso_jointHistogram {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) (k r : ℕ) :
    Finset.univ.val.map (jointColor G k r) = Finset.univ.val.map (jointColor H k r) := by
  apply finite_histogram_equiv (Equiv.arrowCongr (Equiv.refl (Fin k)) e.toEquiv)
  exact iso_jointColor G H e k r

lemma iso_separateHistogram {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) (k r : ℕ) :
    Finset.univ.val.map (separateColor G k r) = Finset.univ.val.map (separateColor H k r) := by
  apply finite_histogram_equiv (Equiv.arrowCongr (Equiv.refl (Fin k)) e.toEquiv)
  exact iso_separateColor G H e k r

lemma iso_sameHistogram {V V' W W' : Type} [Fintype V] [Fintype V'] [Fintype W] [Fintype W']
    (G : SimpleGraph V) (G' : SimpleGraph V') (H : SimpleGraph W) (H' : SimpleGraph W')
    (e : G ≃g G') (f : H ≃g H') (c : Convention) (k r : ℕ) :
    sameHistogram G H c k r ↔ sameHistogram G' H' c k r := by
  cases c
  · simp only [sameHistogram, iso_jointHistogram G G' e, iso_jointHistogram H H' f]
  · simp only [sameHistogram, iso_separateHistogram G G' e, iso_separateHistogram H H' f]

lemma iso_samePureHistogram {V V' W W' : Type} [Fintype V] [Fintype V'] [Fintype W] [Fintype W']
    (G : SimpleGraph V) (G' : SimpleGraph V') (H : SimpleGraph W) (H' : SimpleGraph W')
    (e : G ≃g G') (f : H ≃g H') (c : Convention) (k r : ℕ) :
    samePureHistogram G H c k r ↔ samePureHistogram G' H' c k r := by
  let E := e.sumCongr f
  have hj₁ : Finset.univ.val.map (fun x : Fin k → V => jointColor (G.sum H) k r (Sum.inl ∘ x)) =
      Finset.univ.val.map (fun x : Fin k → V' => jointColor (G'.sum H') k r (Sum.inl ∘ x)) := by
    apply finite_histogram_equiv (Equiv.arrowCongr (Equiv.refl (Fin k)) e.toEquiv)
    intro x
    exact iso_jointColor _ _ E k r _
  have hj₂ : Finset.univ.val.map (fun x : Fin k → W => jointColor (G.sum H) k r (Sum.inr ∘ x)) =
      Finset.univ.val.map (fun x : Fin k → W' => jointColor (G'.sum H') k r (Sum.inr ∘ x)) := by
    apply finite_histogram_equiv (Equiv.arrowCongr (Equiv.refl (Fin k)) f.toEquiv)
    intro x
    exact iso_jointColor _ _ E k r _
  have hs₁ : Finset.univ.val.map (fun x : Fin k → V => separateColor (G.sum H) k r (Sum.inl ∘ x)) =
      Finset.univ.val.map (fun x : Fin k → V' => separateColor (G'.sum H') k r (Sum.inl ∘ x)) := by
    apply finite_histogram_equiv (Equiv.arrowCongr (Equiv.refl (Fin k)) e.toEquiv)
    intro x
    exact iso_separateColor _ _ E k r _
  have hs₂ : Finset.univ.val.map (fun x : Fin k → W => separateColor (G.sum H) k r (Sum.inr ∘ x)) =
      Finset.univ.val.map (fun x : Fin k → W' => separateColor (G'.sum H') k r (Sum.inr ∘ x)) := by
    apply finite_histogram_equiv (Equiv.arrowCongr (Equiv.refl (Fin k)) f.toEquiv)
    intro x
    exact iso_separateColor _ _ E k r _
  cases c
  · simp only [samePureHistogram, hj₁, hj₂]
  · simp only [samePureHistogram, hs₁, hs₂]

lemma iso_WLEquivalent {V V' W W' : Type} [Fintype V] [Fintype V'] [Fintype W] [Fintype W']
    (G : SimpleGraph V) (G' : SimpleGraph V') (H : SimpleGraph W) (H' : SimpleGraph W')
    (e : G ≃g G') (f : H ≃g H') (c : Convention) (k : ℕ) :
    WLEquivalent G H c k ↔ WLEquivalent G' H' c k :=
  forall_congr' (iso_sameHistogram G G' H H' e f c k)

lemma iso_PureWLEquivalent {V V' W W' : Type} [Fintype V] [Fintype V'] [Fintype W] [Fintype W']
    (G : SimpleGraph V) (G' : SimpleGraph V') (H : SimpleGraph W) (H' : SimpleGraph W')
    (e : G ≃g G') (f : H ≃g H') (c : Convention) (k : ℕ) :
    PureWLEquivalent G H c k ↔ PureWLEquivalent G' H' c k :=
  forall_congr' (iso_samePureHistogram G G' H H' e f c k)

end ParityWL

end OAI
