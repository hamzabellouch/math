import OAI.Combinatorics.TreewidthL1.LaunchNoise

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1
open MeasureTheory LaunchNoise AnchorTreeParticles
attribute [local instance] Classical.decEq Classical.propDecidable

theorem anchor_embedding_preparation (k : ℕ) (hk : 2 ≤ k) :
    ∃ α π : ℝ, 0 < α ∧ α ≤ 1/8 ∧ 0 < π ∧ π ≤ 1 ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
      (m : ℕ) (T : SimpleGraph (Fin m)) (hT : T.IsTree) (root : Fin m)
      (B : Fin m → Finset V) (hne : ∀ i, (B i).Nonempty)
      (_ : ∀ v, ∃ i, v ∈ B i)
      (_ : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
      (_ : ∀ v, (T.induce {i | v ∈ B i}).Connected)
      (_ : ∀ i, (B i).card ≤ k) (J η : ℝ), 0 < η → η < 1/4 →
    let := weightedMetricSpace G ℓ hG hℓ
    let D := fun i => bagDistance G ℓ (B i) (hne i)
    ∃ seed : (i : Fin m) → OrdinarySeed (D i) α π η,
    let Ω := (i : Fin m) → NoiseSpace (seed i).n (seed i).m
    let law : Measure Ω := Measure.pi (fun i => noiseLaw (seed i).m (seed i).mass)
    let A := TreeCache.active T hT root B D k (shortestPathDistance G ℓ) J
    let N := 2*(AnchorCache.cacheBound k+1) + k.factorial + 2
    let g : Ω → Fin m → Fin m → V → ℝ :=
      fun ω i _ => noiseG (D i) (seed i).bump (ω i)
    let S := fun ω => state (ι := Fin N) (RootedTree.forest T hT root) B A (g ω)
    ∃ H : ℝ, 0 < H ∧ IsProbabilityMeasure law ∧
      (∀ i a v, Measurable (fun ω => g ω i a v)) ∧
      (∀ ω i, FunctionParticleReachable (shortestPathDistance G ℓ) 3 H (S ω i).1) ∧
      (∀ ω i p, (RootedTree.forest T hT root).parent i = some p →
        particleTrace (H*((N:ℝ)-1)+2) (S ω i).1 (B i) =
          particleTrace (H*((N:ℝ)-1)+2) (S ω p).1 (B i)) ∧
      (∀ ω i p, (RootedTree.forest T hT root).parent i = some p → ∀ a ∈ A i ∩ A p,
        (S ω i).2 a = (S ω p).2 a ∧
        (S ω i).1 ((S ω i).2 a).1 = (S ω p).1 ((S ω p).2 a).1 ∧
        (S ω i).1 ((S ω i).2 a).2 = (S ω p).1 ((S ω p).2 a).2) ∧
      ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        (∀ u v, ‖Φ u - Φ v‖ ≤ 3*(N:ℝ)*((N:ℝ)-1)*shortestPathDistance G ℓ u v) ∧
        ∀ i a, a ∈ A i → ∀ (u v : B i),
          2*(∫ ω, |g ω a a u - g ω a a v| ∂law) ≤ ‖Φ u.val - Φ v.val‖ := by
  classical
  obtain ⟨α,π,hα,hα8,hπ,hπ1,hsampler⟩ := graph_ordinary_noise k hk
  refine ⟨α,π,hα,hα8,hπ,hπ1,?_⟩
  intro V _ _ _ G hG ℓ hℓ m T hT root B hne hcover hedge hrun hbag J η hη hη4
  let := weightedMetricSpace G ℓ hG hℓ
  let D := fun i => bagDistance G ℓ (B i) (hne i)
  have hdec : HasTreeDecomposition G k := ⟨m,T,B,hT,hcover,hedge,hrun,hbag⟩
  have hnoise (i : Fin m) : HasOrdinaryNoise (D i) α π η := by
    have hn := hsampler V G hG hdec ℓ hℓ (B i : Set V) (hne i) η hη hη4
    have heq : D i = fun x => Metric.infDist x (B i : Set V) := by
      funext x
      exact bagDistance_eq_infDist G hG ℓ hℓ (B i) (hne i) x
    rw [heq]
    exact hn
  let seed : (i : Fin m) → OrdinarySeed (D i) α π η :=
    fun i => Classical.choice (OrdinarySeed.exists_of_has (hnoise i))
  refine ⟨seed,?_⟩
  let Ω := (i : Fin m) → NoiseSpace (seed i).n (seed i).m
  let (i : Fin m) : IsProbabilityMeasure (noiseLaw (seed i).m (seed i).mass) := (seed i).probability
  let law : Measure Ω := Measure.pi (fun i => noiseLaw (seed i).m (seed i).mass)
  let A := TreeCache.active T hT root B D k (shortestPathDistance G ℓ) J
  let q := AnchorCache.cacheBound k+1
  let N := 2*q+k.factorial+2
  have hN : 2 ≤ N := by dsimp [N]; omega
  let g : Ω → Fin m → Fin m → V → ℝ := fun ω i _ => noiseG (D i) (seed i).bump (ω i)
  let R := RootedTree.forest T hT root
  let S := fun ω => state (ι := Fin N) R B A (g ω)
  let H : ℝ := 1+3*∑ i, ∑ v, D i v
  have hD : ∀ i v, 0 ≤ D i v := fun i v =>
    bagDistance_nonneg G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) v
  have hsum : 0 ≤ ∑ i, ∑ v, D i v :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun v _ => hD i v))
  have hH : 0 < H := by dsimp [H]; positivity
  have hdH (i : Fin m) (v : V) : (5/2)*D i v ≤ H := by
    have hv := Finset.single_le_sum (fun x (_ : x ∈ (Finset.univ : Finset V)) => hD i x)
      (Finset.mem_univ v)
    have hi : (∑ x, D i x) ≤ ∑ j, ∑ x, D j x :=
      Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
        Finset.sum_nonneg (fun x _ => hD j x)) (Finset.mem_univ i)
    dsimp [H]
    linarith [hD i v]
  have hg : ∀ i a v, Measurable (fun ω : Ω => g ω i a v) := by
    intro i a v
    exact ((measurable_pi_apply v).comp (seed i).measurable).comp (measurable_pi_apply i)
  have hLip : ∀ ω i a, ∀ u v, |g ω i a u-g ω i a v| ≤ 3*shortestPathDistance G ℓ u v := by
    intro ω i a u v
    exact ((seed i).bounds (ω i)).2.2.1.dist_le_mul u v
  have hHeight : ∀ ω i a v, |g ω i a v| ≤ H := by
    intro ω i a v
    have hb := ((seed i).bounds (ω i)).2.2.2 v
    rw [abs_of_nonneg ((hD i v).trans hb.1)]
    exact hb.2.trans (hdH i v)
  have hz : ∀ ω i a, ∀ v ∈ B i, g ω i a v = 0 := by
    intro ω i a v hv
    have hb := ((seed i).bounds (ω i)).2.2.2 v
    have he : D i v = 0 := by
      rw [show D i v = Metric.infDist v (B i : Set V) from
        bagDistance_eq_infDist G hG ℓ hℓ (B i) (hne i) v]
      exact Metric.infDist_zero_of_mem hv
    rw [he] at hb
    dsimp only [g]
    linarith
  have hA : ∀ i, (A i).card ≤ q :=
    TreeCache.graph_active_bound G ℓ hG hℓ T B hne hT root hedge hrun k hbag J
  have hf (ω : Ω) := forest_particle_realization (ι := Fin N) R B A k q hbag hA
    (by simp [N]) (shortestPathDistance G ℓ) 3 H 1 hH (by norm_num)
    (g ω) (hLip ω) (hHeight ω) (hz ω)
  refine ⟨H,hH,inferInstance,hg,?_,?_,?_,?_⟩
  · intro ω i
    exact (hf ω).1 i
  · intro ω i p hp
    simpa only [Fintype.card_fin,mul_one] using (hf ω).2.1 i p hp
  · intro ω i p hp a ha
    exact (hf ω).2.2.1 i p hp a ha
  · obtain ⟨n,Φ,hup,hlo⟩ := averaged_origin_realization (ι := Fin N) G hG ℓ hℓ T hT root B
      hcover hedge (fun v => (hrun v).preconnected) A k q hbag hA (by simp [N])
      law 3 H 1 (by norm_num) hH (by norm_num) g hg hLip hHeight hz
    refine ⟨n,Φ,?_,?_⟩
    · intro u v
      simpa only [Fintype.card_fin,mul_comm (N:ℝ) 3] using hup u v
    · intro i a ha u v
      have hh := hlo i a ha u v
      have ho : origin R A root i a = a := by
        have hh := TreeCache.origin_self T hT root B D k (shortestPathDistance G ℓ) J i a ha
        have hd : (Classical.decEq (Fin m)) = (instDecidableEqFin m) := Subsingleton.elim _ _
        rw [hd] at hh
        exact hh
      rwa [ho] at hh
end BoundedTreewidthL1

namespace BoundedTreewidthL1

lemma marginal_mono {A C : Type*} [Fintype A]
    (f : A → C) {μ ν : A → ℝ} (h : ∀ a, μ a ≤ ν a) (c : C) :
    marginal f μ c ≤ marginal f ν c := by
  classical
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> simp_all

lemma marginal_add {A C : Type*} [Fintype A]
    (f : A → C) (μ ν : A → ℝ) (c : C) :
    marginal f (μ + ν) c = marginal f μ c + marginal f ν c := by
  classical
  unfold marginal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma marginal_smul {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (r : ℝ) (c : C) :
    marginal f (r • μ) c = r * marginal f μ c := by
  classical
  unfold marginal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma marginal_comp {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → B) (g : B → C) (μ : A → ℝ) (c : C) :
    marginal g (marginal f μ) c = marginal (g ∘ f) μ c := by
  classical
  unfold marginal
  have hexpand : (∑ b : B, if g b = c then ∑ a : A, if f a = b then μ a else 0 else 0) =
      ∑ b : B, ∑ a : A, if g b = c then (if f a = b then μ a else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp
  rw [hexpand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  trans ∑ b : B, if f a = b then (if g b = c then μ a else 0) else 0
  · apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> rfl
  · simp

lemma marginal_total {A C : Type*} [Fintype A] [Fintype C]
    (f : A → C) (μ : A → ℝ) : (∑ c, marginal f μ c) = ∑ a, μ a := by
  classical
  simp only [marginal]
  rw [Finset.sum_comm]
  simp

lemma glueWeights_row_formula {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ) (a : A) :
    (∑ b, glueWeights f g μ ν a b) =
      μ a * marginal g ν (f a) / marginal f μ (f a) := by
  classical
  simp only [marginal, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  unfold glueWeights marginal
  by_cases h : f a = g b
  · simp only [h, ↓reduceIte]
  · simp [h, Ne.symm h]

lemma glueWeights_col_formula {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ) (b : B) :
    (∑ a, glueWeights f g μ ν a b) =
      marginal f μ (g b) * ν b / marginal f μ (g b) := by
  classical
  rw [marginal, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  unfold glueWeights
  by_cases h : f a = g b
  · simp [h, marginal]
  · simp [h]

theorem glueWeights_of_submarginal {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b)
    (hdom : ∀ c, marginal g ν c ≤ marginal f μ c) :
    (∀ a b, 0 ≤ glueWeights f g μ ν a b) ∧
    (∀ a, (∑ b, glueWeights f g μ ν a b) ≤ μ a) ∧
    (∀ b, (∑ a, glueWeights f g μ ν a b) = ν b) := by
  refine ⟨glueWeights_nonneg f g μ ν hμ hν, ?_, ?_⟩
  · intro a
    rw [glueWeights_row_formula]
    by_cases hm : marginal f μ (f a) = 0
    · simp [hm, hμ a]
    · apply (div_le_iff₀ (lt_of_le_of_ne (marginal_nonneg f μ hμ _) (Ne.symm hm))).mpr
      exact mul_le_mul_of_nonneg_left (hdom _) (hμ a)
  · intro b
    rw [glueWeights_col_formula]
    by_cases hm : marginal f μ (g b) = 0
    · have hn : ν b = 0 := by
        have h1 := le_marginal g ν hν b
        have h2 := hdom (g b)
        rw [hm] at h2
        exact le_antisymm (h1.trans h2) (hν b)
      simp [hm, hn]
    · exact mul_div_cancel_left₀ (ν b) hm

end BoundedTreewidthL1

namespace BoundedTreewidthL1.ExpandedParticleKernel
open scoped BigOperators

/-- A finite transition coupling. We compose couplings, not stochastic kernels,
so zero-mass states require no arbitrary probability distribution. -/
noncomputable def compose {A B C : Type*} [Fintype B]
    (μ : B → ℝ) (J : A → B → ℝ) (K : B → C → ℝ) (a : A) (c : C) : ℝ :=
  ∑ b, J a b * K b c / μ b

 theorem retained_or_free_marginal {A B C : Type*} [Fintype A]
    (key : A → Option B) (trace : A → C) (μ ν : A → ℝ)
    (hret : ∀ a, key a ≠ none → μ a = ν a)
    (ht : ∀ c, marginal trace μ c = marginal trace ν c) :
    ∀ z, marginal (fun a => (key a, trace a)) μ z =
      marginal (fun a => (key a, trace a)) ν z := by
  classical
  rintro ⟨k, c⟩
  cases k with
  | some b =>
    unfold marginal
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : (key a, trace a) = (some b, c)
    · have hk : key a = some b := congrArg Prod.fst h
      have he := hret a (by simp [hk])
      simp only [h, ↓reduceIte, he]
    · simp only [h, ↓reduceIte]
  | none =>
    have he : (∑ a, if key a ≠ none ∧ trace a = c then μ a else 0) =
        ∑ a, if key a ≠ none ∧ trace a = c then ν a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs with h
      · exact hret a h.1
      · rfl
    have hs (ρ : A → ℝ) : marginal trace ρ c =
        marginal (fun a => (key a, trace a)) ρ (none, c) +
        ∑ a, if key a ≠ none ∧ trace a = c then ρ a else 0 := by
      unfold marginal
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hk : key a = none <;> by_cases ht : trace a = c <;> simp [hk, ht]
    have ha := ht c
    rw [hs μ, hs ν, he] at ha
    exact add_right_cancel ha

 theorem compose_coupling {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : A → ℝ) (ν : B → ℝ) (ξ : C → ℝ)
    (J : A → B → ℝ) (K : B → C → ℝ)
    (_ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (_ : ∀ c, 0 ≤ ξ c)
    (hJ : ∀ a b, 0 ≤ J a b) (hK : ∀ b c, 0 ≤ K b c)
    (hrJ : ∀ a, ∑ b, J a b = μ a) (hcJ : ∀ b, ∑ a, J a b = ν b)
    (hrK : ∀ b, ∑ c, K b c = ν b) (hcK : ∀ c, ∑ b, K b c = ξ c) :
    (∀ a c, 0 ≤ compose ν J K a c) ∧
    (∀ a, ∑ c, compose ν J K a c = μ a) ∧
    (∀ c, ∑ a, compose ν J K a c = ξ c) := by
  classical
  have hJ0 (b : B) (hb : ν b = 0) : ∀ a, J a b = 0 := by
    intro a
    have h := Finset.single_le_sum (s := Finset.univ) (fun a _ => hJ a b)
      (Finset.mem_univ a)
    rw [hcJ, hb] at h
    exact le_antisymm h (hJ a b)
  have hK0 (b : B) (hb : ν b = 0) : ∀ c, K b c = 0 := by
    intro c
    have h := Finset.single_le_sum (s := Finset.univ) (fun c _ => hK b c)
      (Finset.mem_univ c)
    rw [hrK, hb] at h
    exact le_antisymm h (hK b c)
  refine ⟨fun a c => Finset.sum_nonneg (fun b _ =>
    div_nonneg (mul_nonneg (hJ a b) (hK b c)) (hν b)), ?_, ?_⟩
  · intro a
    unfold compose
    rw [Finset.sum_comm]
    have he (b : B) : (∑ c, J a b * K b c / ν b) = J a b := by
      rw [← Finset.sum_div, ← Finset.mul_sum, hrK]
      by_cases hb : ν b = 0
      · simp [hb, hJ0 b hb a]
      · exact mul_div_cancel_right₀ (J a b) hb
    simp_rw [he]
    exact hrJ a
  · intro c
    unfold compose
    rw [Finset.sum_comm]
    have he (b : B) : (∑ a, J a b * K b c / ν b) = K b c := by
      rw [← Finset.sum_div, ← Finset.sum_mul, hcJ]
      by_cases hb : ν b = 0
      · simp [hb, hK0 b hb c]
      · exact mul_div_cancel_left₀ (K b c) hb
    simp_rw [he]
    exact hcK c

 theorem compose_trace {A B C D : Type*} [Fintype B]
    (ν : B → ℝ) (J : A → B → ℝ) (K : B → C → ℝ)
    (f : A → D) (g : B → D) (h : C → D)
    (hJ : ∀ a b, f a ≠ g b → J a b = 0)
    (hK : ∀ b c, g b ≠ h c → K b c = 0)
    (a : A) (c : C) (hne : f a ≠ h c) : compose ν J K a c = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro b _
  by_cases hfg : f a = g b
  · have hgh : g b ≠ h c := fun he => hne (hfg.trans he)
    simp [hK b c hgh]
  · simp [hJ a b hfg]

end BoundedTreewidthL1.ExpandedParticleKernel

namespace BoundedTreewidthL1.ExpandedParticleLaw
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

abbrev State (ι V : Type*) := ι × Bool × (V → Bool)

def label (a : State ι V) (v : V) : Bool :=
  if a.2.1 then !(a.2.2 v) else a.2.2 v

noncomputable def weight (M : ℝ) (F : ι → V → ℝ) (a : State ι V) : ℝ :=
  (sweep M (F a.1)).real {a.2.2} / 2

def trace (P : Finset V) (a : State ι V) : P → Bool := fun v => label a v

/-- At incoming updates, the entire state is retained on protected particles.
Every remaining state is pooled in one free class. -/
noncomputable def incomingKey (C : Finset ι) (a : State ι V) : Option (State ι V) :=
  if a.1 ∈ C then some a else none

/-- Departure reheats the fresh pair jointly and every other index separately.
Orientation is retained in either case. -/
noncomputable def departureKey (a b : ι) (x : State ι V) : ι × Bool :=
  (if x.1 = b then a else x.1, x.2.1)

noncomputable def incoming (M : ℝ) (F H : ι → V → ℝ) (P : Finset V) (C : Finset ι) :=
  glueWeights (fun a => (incomingKey C a, trace P a))
    (fun a => (incomingKey C a, trace P a)) (weight M F) (weight M H)

noncomputable def departure (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (a b : ι) :=
  glueWeights (fun x => (departureKey a b x, trace P x))
    (fun x => (departureKey a b x, trace P x)) (weight M F) (weight M F)

lemma weight_nonneg
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι]
    (M : ℝ) (F : ι → V → ℝ) (a : State ι V) : 0 ≤ weight M F a :=
  div_nonneg measureReal_nonneg (by norm_num)

lemma finite_event {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsFiniteMeasure μ] (p : A → Prop) :
    (∑ a, if p a then μ.real {a} else 0) = μ.real {a | p a} := by
  classical
  have h := sum_measureReal_singleton (μ := μ) (Finset.univ.filter p)
  simpa only [Finset.sum_filter, Finset.coe_filter, Finset.coe_univ,
    Finset.mem_univ, true_and] using h

lemma oriented_marginal (M : ℝ) (F : V → ℝ) (P : Finset V) (b : P → Bool) :
    (∑ q : Bool, ∑ ω : V → Bool,
      if (fun v : P => if q then !(ω v) else ω v) = b then
        (sweep M F).real {ω}/2 else 0) =
      (symmetrizeCut (sweep M F)).real {ω | (fun v : P => ω v) = b} := by
  classical
  rw [Fintype.sum_bool]
  have ht : (∑ ω : V → Bool,
      if (fun v : P => !(ω v)) = b then (sweep M F).real {ω}/2 else 0) =
      (sweep M F).real {ω | (fun v : P => !(ω v)) = b}/2 := by
    rw [← finite_event, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  have hf : (∑ ω : V → Bool,
      if (fun v : P => ω v) = b then (sweep M F).real {ω}/2 else 0) =
      (sweep M F).real {ω | (fun v : P => ω v) = b}/2 := by
    rw [← finite_event, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [ht, hf, symmetrizeCut, measureReal_ennreal_smul_apply,
    measureReal_add_apply (by finiteness) (by finiteness),
    map_measureReal_apply measurable_complementCut (Set.toFinite _).measurableSet]
  have he : complementCut ⁻¹' {ω : V → Bool | (fun v : P => ω v) = b} =
      {ω : V → Bool | (fun v : P => !(ω v)) = b} := rfl
  rw [he]
  norm_num
  ring

/-- Exact original symmetric bag trace; no change of the prepared marginal. -/
 theorem trace_marginal (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (b : P → Bool) :
    marginal (trace P) (weight M F) b = (particleTrace M F P).real {b} := by
  classical
  unfold marginal
  simp only [Fintype.sum_prod_type]
  have he (i : ι) : (∑ x : Bool, ∑ ω : V → Bool,
      if trace P (i,x,ω) = b then weight M F (i,x,ω) else 0) =
        (symmetrizeCut (sweep M (F i))).real {ω | (fun v : P => ω v) = b} :=
    oriented_marginal M (F i) P b
  trans ∑ i, (symmetrizeCut (sweep M (F i))).real {ω | (fun v : P => ω v) = b}
  · apply Finset.sum_congr rfl
    intro i _
    convert he i using 1
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> rfl
  rw [particleTrace, measureReal_def, Measure.finsetSum_apply,
    ENNReal.toReal_sum (fun i _ => by unfold cutTrace; finiteness)]
  apply Finset.sum_congr rfl
  intro i _
  exact (map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton b)).symm

 theorem incoming_coupling (M : ℝ) (F H : ι → V → ℝ) (P : Finset V) (C : Finset ι)
    (hret : ∀ i ∈ C, F i = H i) (htrace : particleTrace M F P = particleTrace M H P) :
    (∀ a b, 0 ≤ incoming M F H P C a b) ∧
    (∀ a, ∑ b, incoming M F H P C a b = weight M F a) ∧
    (∀ b, ∑ a, incoming M F H P C a b = weight M H b) ∧
    (∀ a b, trace P a ≠ trace P b → incoming M F H P C a b = 0) ∧
    (∀ a b, a.1 ∈ C → a ≠ b → incoming M F H P C a b = 0) := by
  classical
  have ht (b : P → Bool) : marginal (trace P) (weight M F) b =
      marginal (trace P) (weight M H) b := by rw [trace_marginal, trace_marginal, htrace]
  have hr (a : State ι V) (ha : incomingKey C a ≠ none) : weight M F a = weight M H a := by
    have hc : a.1 ∈ C := by simpa [incomingKey] using ha
    unfold weight
    rw [hret a.1 hc]
  have hcons := ExpandedParticleKernel.retained_or_free_marginal
    (incomingKey C) (trace P) (weight M F) (weight M H) hr ht
  refine ⟨glueWeights_nonneg _ _ _ _ (weight_nonneg M F) (weight_nonneg M H),
    glueWeights_row _ _ _ _ (weight_nonneg M F) hcons,
    (glueWeights_marginals _ _ _ _ (weight_nonneg M F) (weight_nonneg M H) hcons).2.2, ?_, ?_⟩
  · intro a b hab
    unfold incoming glueWeights
    have he : (incomingKey C a, trace P a) ≠ (incomingKey C b, trace P b) :=
      fun h => hab (congrArg Prod.snd h)
    simp [he]
  · intro a b ha hab
    unfold incoming glueWeights
    have he : (incomingKey C a, trace P a) ≠ (incomingKey C b, trace P b) := by
      intro h
      have hk : incomingKey C a = incomingKey C b := congrArg Prod.fst h
      simp only [incomingKey, ha, ↓reduceIte] at hk
      split_ifs at hk with hb
      · exact hab (Option.some.inj hk)
    simp [he]

 theorem departure_coupling (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j : ι) :
    (∀ a b, 0 ≤ departure M F P i j a b) ∧
    (∀ a, ∑ b, departure M F P i j a b = weight M F a) ∧
    (∀ b, ∑ a, departure M F P i j a b = weight M F b) ∧
    (∀ a b, trace P a ≠ trace P b → departure M F P i j a b = 0) ∧
    (∀ a b, departureKey i j a ≠ departureKey i j b → departure M F P i j a b = 0) := by
  classical
  have hc : ∀ c, marginal (fun x => (departureKey i j x, trace P x)) (weight M F) c =
      marginal (fun x => (departureKey i j x, trace P x)) (weight M F) c := fun _ => rfl
  refine ⟨glueWeights_nonneg _ _ _ _ (weight_nonneg M F) (weight_nonneg M F),
    glueWeights_row _ _ _ _ (weight_nonneg M F) hc,
    (glueWeights_marginals _ _ _ _ (weight_nonneg M F) (weight_nonneg M F) hc).2.2, ?_, ?_⟩
  · intro a b hab
    unfold departure glueWeights
    have he : (departureKey i j a, trace P a) ≠ (departureKey i j b, trace P b) :=
      fun h => hab (congrArg Prod.snd h)
    simp [he]
  · intro a b hab
    unfold departure glueWeights
    have he : (departureKey i j a, trace P a) ≠ (departureKey i j b, trace P b) :=
      fun h => hab (congrArg Prod.fst h)
    simp [he]

end BoundedTreewidthL1.ExpandedParticleLaw

end OAI
