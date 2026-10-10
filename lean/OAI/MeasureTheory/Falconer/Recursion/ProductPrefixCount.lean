import OAI.MeasureTheory.Falconer.Estimates.ProductCandidateWidth
import OAI.MeasureTheory.Falconer.Recursion.PrefixMass

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem candidate_prefix_card_le {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (A : CellPath) (C : Finset CellPath) (hC : C ⊆ dyadicPaths p)
    (hparent : ∀ c ∈ C, c.take a = A) :
    (C.image (List.take g)).card ≤ 4^(g-a) := by
  classical
  have hsub : C.image (List.take g) ⊆ (dyadicPaths (g-a)).image (fun c => A++c) := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    have hl := (mem_dyadicPaths _ _).mp (hC hc)
    refine Finset.mem_image.mpr ⟨(c.take g).drop a,?_,?_⟩
    · simp [mem_dyadicPaths,List.length_take,hl,hgp]
    · simpa only [List.take_take,Nat.min_eq_left hag,hparent c hc] using
        List.take_append_drop a (c.take g)
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans (dyadicPaths_card_le (g-a)))

theorem candidate_card_le_prefix_groups {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (A : CellPath) (C : Finset CellPath) (hC : C ⊆ dyadicPaths p)
    (hparent : ∀ c ∈ C, c.take a = A) (b : ℝ) (hb : 0 ≤ b)
    (hgroup : ∀ G ∈ C.image (List.take g), ((prefixFiber C g G).card : ℝ) ≤ b) :
    (C.card : ℝ) ≤ (4:ℝ)^(g-a)*b := by
  classical
  have he : C.card = ∑ G ∈ C.image (List.take g), (prefixFiber C g G).card :=
    Finset.card_eq_sum_card_image (List.take g) C
  calc
    _ = ∑ G ∈ C.image (List.take g), ((prefixFiber C g G).card : ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _G ∈ C.image (List.take g), b := Finset.sum_le_sum hgroup
    _ = ((C.image (List.take g)).card : ℝ)*b := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast candidate_prefix_card_le hag hgp A C hC hparent) hb

theorem height_mono_start (m : ℕ → ℝ) {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p) :
    height m g p ≤ height m a p := by
  obtain ⟨t,hgt,htp,he⟩ := intervalMin_attained m hgp
  have hh := intervalMin_le m (hag.trans hgt) htp
  unfold height
  rw [he]
  linarith

theorem coarse_prefix_power {a g N : ℕ} (hag : a ≤ g) {sig : ℝ}
    (hgap : (g:ℝ)-a ≤ 2*sig*N) : (4:ℝ)^(g-a) ≤ ((2:ℝ)^N)^(4*sig) := by
  have he : (4:ℝ)^(g-a) = (2:ℝ)^(2*((g:ℝ)-a)) := by
    rw [← Nat.cast_sub hag,show (4:ℝ) = 2^2 by norm_num,← pow_mul]
    norm_cast
  rw [he,← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

theorem uniform_inherited_product_candidate_count {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ), i < J → ∀ h : Plane → ℂ, ∀ e ∈ S, ∀ a g p : ℕ,
    d e = .parallel g p → a ≤ g → g ≤ p → p ≤ N → (g:ℝ)-a ≤ 2*sig*N →
    ∀ (A : CellPath) (C : Finset CellPath), C ⊆ occupiedAnchorPaths Q ρ p →
    (∀ c ∈ C, c.take a = A) →
    ∀ (z : Plane) (u : UnitCircle) (c₀ : ℝ), 0 < c₀ → c₀ ≤ 2*Real.pi →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    ∀ j : ℕ, u ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    (∀ c ∈ C, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ 5*graphNonedgeThreshold N sig p) →
    (∀ c ∈ C, AngularLabelEligible ρ (Q.descendant c).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) (angularBinCount θ) j) →
    (C.card : ℝ) ≤ ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)+4*sig) := by
  obtain ⟨N₀,hcount⟩ := uniform_inherited_product_group_count hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i hi h e he a g p hd hag hgp hp hgap A C hC hparent z u c₀ hc hcap
  dsimp only
  intro j hu hstrip hel
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hpaths : C ⊆ dyadicPaths p := fun c hc => (Finset.mem_filter.mp (hC hc)).1
  have hb := candidate_card_le_prefix_groups hag hgp A C hpaths hparent
    (((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) g p+2000*(lam+sig))) (by positivity) (by
      intro G hG
      have hlen : G.length = g := by
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hG
        have hl := (mem_dyadicPaths _ _).mp (hpaths hc)
        simp [List.length_take,hl,hgp]
      exact hcount N hN S d k Q hQ ρ m lam i hi h e he a g p hd hag hgp hp G hlen
        (prefixFiber C g G) (fun c hc => hC (Finset.mem_filter.mp hc).1)
        (by
          intro c hc
          obtain ⟨hc,he⟩ := Finset.mem_filter.mp hc
          rw [← he]
          exact Q.descendant_subset_take hQpos c g)
        z u c₀ hc hcap j hu
        (fun c hc => hstrip c (Finset.mem_filter.mp hc).1)
        (fun c hc => hel c (Finset.mem_filter.mp hc).1))
  have hh : ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) g p+2000*(lam+sig)) ≤
      ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
      (add_le_add (height_mono_start _ hag hgp) le_rfl)
  calc
    _ ≤ _ := hb
    _ ≤ ((2:ℝ)^N)^(4*sig)*((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)) :=
      mul_le_mul (coarse_prefix_power hag hgap) hh (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]; congr 1; ring

end PlanarFalconer

end OAI
