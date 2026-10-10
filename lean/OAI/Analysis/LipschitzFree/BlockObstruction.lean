import OAI.Analysis.LipschitzFree.Parameters
import OAI.Analysis.LipschitzFree.ScalarTests
import OAI.Analysis.LipschitzFree.GraphSequence

namespace OAI

/-!
# Signed finite-rank obstruction on countable bounded metric blocks
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.BlockConstruction
open scoped Classical BigOperators
open BlockParameters

abbrev Generators (p : ℕ) := Fin (generators p)
abbrev Colors (p : ℕ) := Fin (colors p)
abbrev Ports (p : ℕ) := Generators p × Bool
abbrev Vertices (p : ℕ) := GraphProducer.Vertex (Generators p) (Colors p)

instance (p : ℕ) : Nonempty (Colors p) := ⟨⟨0,colors_pos p⟩⟩
instance (p : ℕ) : Nonempty (Ports p) := ⟨⟨⟨0,by dsimp [generators]; omega⟩,true⟩⟩

def graph (p : ℕ) := GraphProducer.sequenceGraph (Generators p) (Colors p)
def color (p : ℕ) := GraphProducer.sequenceColor (Generators p) (Colors p)
abbrev Block (p : ℕ) := MetricBlock.Point (graph p) (color p) (D p) (R p)

def baseVertex (p : ℕ) : Vertices p := ⟨0,(fun _ => ⟨0,colors_pos p⟩),1⟩

def base (p : ℕ) : Block p := MetricBlock.ofAnchor (graph p) (color p) (D p) (R p)
  (MetricBlock.anchorOf (graph p) (color p) (D p) (baseVertex p))

def anchors (p : ℕ) : Finset (Block p) := Finset.univ.image
  (MetricBlock.ofAnchor (graph p) (color p) (D p) (R p))

theorem base_mem (p : ℕ) : base p ∈ anchors p :=
  Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

theorem attached_mem (p : ℕ) (x : Vertices p) :
    MetricBlock.ofAnchor (graph p) (color p) (D p) (R p)
      (MetricBlock.anchorOf (graph p) (color p) (D p) x) ∈ anchors p :=
  Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

@[simp] theorem card_ports (p : ℕ) : Fintype.card (Ports p) = degree p := by
  simp [Ports,degree,Nat.mul_comm]

@[simp] theorem nat_card_ports (p : ℕ) : Nat.card (Ports p) = degree p := by
  simp only [Nat.card_eq_fintype_card,card_ports]

@[simp] theorem nat_card_colors (p : ℕ) : Nat.card (Colors p) = colors p := Nat.card_fin _

variable (p : ℕ) [Fact (0 < R p)]

theorem separation (x y : Block p) (h : x ≠ y) : 1 ≤ dist x y :=
  MetricBlock.separated (graph p) (color p) (D p) (R p) h

theorem diameter (x y : Block p) : dist x y ≤ (B p : ℝ) :=
  MetricBlock.diameter_bound (graph p) (color p) (D p) (R p) x y

omit [Fact (0 < R p)] in
theorem support_colors_bound (j : Block p) :
    (MetricBlock.supportColors (graph p) (color p) (D p) (R p) j).card ≤ H p := by
  apply (MetricBlock.supportColors_card (graph p) (color p) (D p) (R p) j).trans
  have hd : 2 ≤ Fintype.card (Ports p) := by rw [card_ports]; have := degree_ge p; omega
  simpa only [card_ports,H] using (BoundedWords.card_lt_pow (D := Ports p) hd (D p)).le

theorem transition_bound (hp : 1 ≤ p) (S : Finset (Block p)) (j : S) :
    Fintype.card {k : S // MetricBlock.Transition (graph p) (color p) (D p) (R p) (L p) j.val k.val} ≤ Q p := by
  apply (MetricBlock.transition_card (graph p) (color p) (D p) (R p) (L p) (small_radius hp) S j).trans
  have hd : 2 ≤ Fintype.card (Ports p) := by rw [card_ports]; have := degree_ge p; omega
  simpa only [card_ports,Q] using (BoundedWords.card_lt_pow (D := Ports p) hd (2*L p)).le

theorem bump_mass (hp : 1 ≤ p) (S : Finset (Block p)) (ho : base p ∈ S)
    (T : FreeSpace (base p) →L[ℝ] FreeSpace (base p))
    (hn : ‖T‖ ≤ 2*(p : ℝ))
    (hfixed : ∀ u, supportProjection (base p) (separation p) S (T u) = T u)
    (he : ∀ a ∈ anchors p, ‖T (delta (base p) a) - delta (base p) a‖ < 1)
    (x : Vertices p) :
    3*(L p : ℝ)/4 ≤
      pairing (affineWeights (base p) (separation p) S ho
        (T (delta (base p) (MetricBlock.ofVertex (graph p) (color p) (D p) (R p) x))))
      (fun j : S => labelBump (MetricBlock.label (graph p) (color p) (D p) (R p))
        (MetricBlock.originalLabel (graph p) (color p) (D p) x) (L p) (K p) j.val) := by
  let vx := MetricBlock.ofVertex (graph p) (color p) (D p) (R p) x
  let ax := MetricBlock.ofAnchor (graph p) (color p) (D p) (R p)
    (MetricBlock.anchorOf (graph p) (color p) (D p) x)
  have hh := affine_bump_mass (base p) (separation p) S ho T hfixed
    (MetricBlock.label (graph p) (color p) (D p) (R p))
    (MetricBlock.label_lipschitz (graph p) (color p) (D p) (R p)) vx ax rfl
    (L p) (K p) p (R p) (Nat.cast_nonneg _) (by exact_mod_cast K_pos hp)
    (Nat.cast_nonneg _) hn (MetricBlock.attachment (graph p) (color p) (D p) (R p) x)
    (he ax (attached_mem p x))
  have hl := bump_loss hp
  change (L p : ℝ) - (L p : ℝ)/(K p : ℝ)*(2*(p : ℝ)*(R p : ℝ)+1) ≤
    pairing _ (fun j : S => labelBump (MetricBlock.label (graph p) (color p) (D p) (R p))
      (MetricBlock.originalLabel (graph p) (color p) (D p) x) (L p) (K p) j.val) at hh
  linarith

theorem finite_support_impossible (hp : 1 ≤ p) (S : Finset (Block p)) (ho : base p ∈ S)
    (T : FreeSpace (base p) →L[ℝ] FreeSpace (base p))
    (hn : ‖T‖ ≤ 2*(p : ℝ))
    (hfixed : ∀ u, supportProjection (base p) (separation p) S (T u) = T u)
    (he : ∀ a ∈ anchors p, ‖T (delta (base p) a) - delta (base p) a‖ < 1) : False := by
  let compatible : Vertices p → S → Prop := fun x j =>
    MetricBlock.Compatible (graph p) (color p) (D p) (R p) (L p) (K p) x j.val
  let trans : S → S → Prop := fun j k =>
    MetricBlock.Transition (graph p) (color p) (D p) (R p) (L p) j.val k.val
  let P : S → Finset (Colors p) := fun j =>
    MetricBlock.supportColors (graph p) (color p) (D p) (R p) j.val
  have hcolor : ∀ x j, compatible x j → color p x ∈ P j := by
    intro x j hj
    exact MetricBlock.compatible_color (graph p) (color p) (D p) (R p) (L p) (K p)
      (compatibility_cap p) x j.val hj
  obtain ⟨n,_,hnrare⟩ := GraphProducer.exists_rare_component (Generators p) (Colors p) S
    (Q p) (H p) (V p) (Q_pos p) (H_pos p) (by rw [nat_card_ports]; have := degree_ge p; omega)
    (by simpa only [nat_card_ports,nat_card_colors] using colors_large p)
    compatible trans P (fun j => support_colors_bound p j.val) hcolor (transition_bound p hp S)
  let X := (GraphProducer.Cayley (Generators p) n → Colors p) × GraphProducer.Cayley (Generators p) n
  let G := GraphProducer.allColoringsGraph (Generators p) (Colors p) n
  let i : X → Vertices p := GraphProducer.intoSequence (Generators p) (Colors p) n
  let v : X → Block p := fun x => MetricBlock.ofVertex (graph p) (color p) (D p) (R p) (i x)
  let μ : X → S → ℝ := fun x => affineWeights (base p) (separation p) S ho (T (delta (base p) (v x)))
  let E : X → Ports p → Set S := fun x e =>
    MetricBlock.exceptionSet (graph p) (color p) (D p) (R p) (L p) (K p) S n (i x) e
  let bad : Finset X := Finset.univ.filter (fun x => ¬ (graph p).Good compatible trans n (i x))
  have hbad : 20*(V p)*(bad.card) < Fintype.card X := by
    have hc : bad.card = Nat.card {x : X // ¬ (graph p).Good compatible trans n (i x)} := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    rw [hc,← Nat.card_eq_fintype_card]
    exact hnrare
  have hrealV : (V p : ℝ) = 1+4*(p : ℝ)*(B p : ℝ) := by simp [V]
  have hTV (x : X) : totalVariation (μ x) ≤ (V p : ℝ) := by
    rw [hrealV]
    exact affineWeights_operator_variation (base p) (separation p) S ho T hfixed p (B p)
      (Nat.cast_nonneg _) hn (fun z => diameter p z (base p)) (v x)
  have hgood (x : X) (hx : x ∉ bad) (j : S) (e f : Ports p)
      (he : j ∈ E x e) (hf : j ∈ E x f) : e = f := by
    have hx' : (graph p).Good compatible trans n (i x) := by
      simpa only [bad,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hx
    exact MetricBlock.exceptional_unique_good (graph p) (color p) (D p) (R p) (L p) (K p)
      S n (i x) hx' j e f he hf
  apply signed_incidence_obstruction μ E bad G.incidenceReverse (p : ℝ) (V p : ℝ)
    (by exact_mod_cast (show 0 < p by omega)) (Nat.cast_nonneg _) hTV hgood
    (by rw [card_ports]; exact_mod_cast degree_variation p) (by exact_mod_cast hbad)
  rintro ⟨x,e⟩
  change 3*(10*(p : ℝ))/2 - 2*(10*(p : ℝ)) *
    (variationOn (μ x) (E x e) + variationOn (μ (G.move x e)) (E (G.move x e) (G.reverse e))) ≤ 2*(p : ℝ)
  obtain ⟨f,hf,hbound,hfx,hfy⟩ := MetricBlock.edge_test (graph p) (color p) (D p) (R p) (L p) (K p)
    (L_pos hp) (K_pos hp) (L_le_K p) S n (i x) e
  let b : S → ℝ := fun j => labelBump (MetricBlock.label (graph p) (color p) (D p) (R p))
    (MetricBlock.originalLabel (graph p) (color p) (D p) (i x)) (L p) (K p) j.val
  let c : S → ℝ := fun j => labelBump (MetricBlock.label (graph p) (color p) (D p) (R p))
    (MetricBlock.originalLabel (graph p) (color p) (D p) (i (G.move x e))) (L p) (K p) j.val
  have hb (j : S) : 0 ≤ b j ∧ b j ≤ (L p : ℝ) :=
    ⟨labelBump_nonneg _ _ (Nat.cast_nonneg _) _,labelBump_le _ _ (Nat.cast_nonneg _) (by exact_mod_cast K_pos hp) _⟩
  have hc (j : S) : 0 ≤ c j ∧ c j ≤ (L p : ℝ) :=
    ⟨labelBump_nonneg _ _ (Nat.cast_nonneg _) _,labelBump_le _ _ (Nat.cast_nonneg _) (by exact_mod_cast K_pos hp) _⟩
  have hlower := opposing_pairing_lower (μ x) (μ (G.move x e)) (fun j : S => f j.val) b c
    (E x e) (E (G.move x e) (G.reverse e)) (L p) (fun j => hbound j.val) hb hc hfx hfy
  have hxmass : 3*(L p : ℝ)/4 ≤ pairing (μ x) b := bump_mass p hp S ho T hn hfixed he (i x)
  have hymass : 3*(L p : ℝ)/4 ≤ pairing (μ (G.move x e)) c := bump_mass p hp S ho T hn hfixed he (i (G.move x e))
  have hdiff := affine_difference_bound (base p) (separation p) S ho T hfixed (2*(p : ℝ)) hn
    f hf (v x) (v (G.move x e))
  have hdist : dist (v x) (v (G.move x e)) ≤ 1 :=
    MetricBlock.source_edge (graph p) (color p) (D p) (R p) (i x) e
  have hupper : pairing (μ x) (fun j : S => f j.val) - pairing (μ (G.move x e)) (fun j : S => f j.val) ≤ 2*(p : ℝ) := by
    apply (le_abs_self _).trans (hdiff.trans _)
    simpa using mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 2*(p : ℝ))
  have hL : (L p : ℝ) = 10*(p : ℝ) := by simp [L]
  rw [hL] at hxmass hymass hlower
  linarith

theorem obstruction (hp : 1 ≤ p)
    (T : FreeSpace (base p) →L[ℝ] FreeSpace (base p))
    (hfin : Module.Finite ℝ (LinearMap.range T.toLinearMap)) (hn : ‖T‖ ≤ (p : ℝ)) :
    ∃ a ∈ anchors p, (1/2 : ℝ) ≤ ‖T (delta (base p) a) - delta (base p) a‖ := by
  by_contra h
  have he : ∀ a ∈ anchors p, ‖T (delta (base p) a) - delta (base p) a‖ < 1/2 := by
    simpa only [not_exists,not_and,not_le] using h
  obtain ⟨S,T₁,ho,_,hT,hfixed,hanchor⟩ := finite_support_reduction (base p) (separation p)
    (B p) p (Nat.cast_nonneg _) (by exact_mod_cast hp) (fun x => diameter p x (base p))
    (anchors p) T hfin hn he
  exact finite_support_impossible p hp S ho T₁ hT hfixed hanchor

theorem original_radius (hp : 1 ≤ p) (x : Vertices p) :
    (R p : ℝ) ≤ dist (MetricBlock.ofVertex (graph p) (color p) (D p) (R p) x) (base p) := by
  by_contra h
  have hh : NatMetricClosure.distance (MetricBlock.weight (graph p) (color p) (D p) (R p))
      (MetricBlock.ofVertex (graph p) (color p) (D p) (R p) x) (base p) < R p := by
    have hlt := lt_of_not_ge h
    rw [MetricBlock.dist_eq] at hlt
    exact_mod_cast hlt
  exact MetricBlock.short_distance (graph p) (color p) (D p) (R p) (R_pos hp) _ _ hh

instance infinite_block : Infinite (Block p) := by
  apply Infinite.of_injective (fun n : ℕ =>
    MetricBlock.ofVertex (graph p) (color p) (D p) (R p)
      (⟨n,(fun _ => ⟨0,colors_pos p⟩),1⟩ : Vertices p))
  intro n m h
  have h' := Sum.inl.inj h
  exact congrArg Sigma.fst h'

end DiscreteFree.BlockConstruction

namespace DiscreteFree

theorem blocks_proved : BlockStatement := by
  intro p hp
  let : Fact (0 < BlockParameters.R p) := ⟨BlockParameters.R_pos hp⟩
  refine ⟨BlockConstruction.Block p,inferInstance,BlockConstruction.base p,inferInstance,
    BlockConstruction.separation p,?_,BlockConstruction.anchors p,BlockConstruction.base_mem p,
    fun T hT hn => BlockConstruction.obstruction p hp T hT hn⟩
  intro x y
  simpa only [BlockParameters.B_formula] using BlockConstruction.diameter p x y
end DiscreteFree
end

end

end OAI
