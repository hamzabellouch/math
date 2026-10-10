import Mathlib
import OAI.Analysis.SymmetricDomains.ContinuityPrinciple

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
open Set
open Filter
open scoped Topology

theorem RelationSteps.trans {X : Type*} {R : X → X → Prop} {m n : ℕ} {x y z : X}
    (hxy : RelationSteps R m x y) (hyz : RelationSteps R n y z) :
    RelationSteps R (m+n) x z := by
  induction n generalizing z with
  | zero => exact hyz ▸ hxy
  | succ n ih =>
      rcases hyz with hyz | ⟨w,hyw,hwz⟩
      · exact Or.inl (ih hyz)
      · exact Or.inr ⟨w,ih hyw,hwz⟩

theorem RelationSteps.single {X : Type*} {R : X → X → Prop} {x y : X} (h : R x y) :
    RelationSteps R 1 x y := Or.inr ⟨x,rfl,h⟩

theorem compact_connected_relation_chains {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (R : X → X → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (hloc : ∀ x, ∀ᶠ y in 𝓝 x, R x y)
    (x : X) {C : Set X} (hC : IsCompact C) :
    ∃ n : ℕ, ∀ y ∈ C, RelationSteps R n x y := by
  classical
  let P : X → X → Prop := fun a b => ∃ n, RelationSteps R n a b
  have htrans : IsTrans X P := ⟨fun _ _ _ h₁ h₂ => by
    obtain ⟨n,hn⟩ := h₁
    obtain ⟨m,hm⟩ := h₂
    exact ⟨n+m,hn.trans hm⟩⟩
  have hP : ∀ y, P x y := PreconnectedSpace.induction₂' P (fun a => by
    filter_upwards [hloc a] with b hb
    exact ⟨⟨1,RelationSteps.single hb⟩,⟨1,RelationSteps.single (hsym a b hb)⟩⟩) htrans x
  choose N hN using hP
  have hnhd : ∀ y, {z | RelationSteps R (N y + 1) x z} ∈ 𝓝 y := by
    intro y
    filter_upwards [hloc y] with z hz
    exact (hN y).trans (RelationSteps.single hz)
  obtain ⟨I,_,hI⟩ := hC.elim_nhds_subcover
    (fun y => {z | RelationSteps R (N y + 1) x z}) (fun y _ => hnhd y)
  refine ⟨I.sup (fun y => N y+1),?_⟩
  intro y hy
  obtain ⟨a,ha,hay⟩ := mem_iUnion₂.mp (hI hy)
  exact RelationSteps.mono (Finset.le_sup (f := fun y => N y+1) ha) hay

theorem IsSmooth.discRelation_nhds {n : ℕ} {U : Set (Affine n)} (hU : IsSmooth U)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x : U) :
    ∀ᶠ y in 𝓝 x, DiscRelation U r x y := by
  classical
  obtain ⟨d,W,hWU,hW,hxW,D,hD,⟨e⟩⟩ := hU x
  let xW : W := ⟨x.val,hxW⟩
  let f : U → W := fun y => if hy : y.val ∈ W then ⟨y.val,hy⟩ else xW
  have hfval : (fun y => (f y).val) =ᶠ[𝓝 x] (fun y : U => y.val) := by
    filter_upwards [hW.mem_nhds hxW] with y hy
    change y.val ∈ W at hy
    simp [f,hy]
  have hfx : f x = xW := by simp [f,xW,hxW]
  have hfc : ContinuousAt f x := by
    apply (Topology.IsEmbedding.subtypeVal.isInducing.continuousAt_iff).mpr
    exact continuous_subtype_val.continuousAt.congr_of_eventuallyEq hfval
  have hec : Tendsto (fun y => e.toHomeomorph (f y)) (𝓝 x) (𝓝 (e.toHomeomorph xW)) := by
    simpa only [Function.comp_def,hfx] using e.toHomeomorph.continuous.continuousAt.tendsto.comp hfc.tendsto
  filter_upwards [hec (open_discRelation_nhds hD hr hr1 (e.toHomeomorph xW)),
    hW.mem_nhds hxW] with y hy hyW
  change y.val ∈ W at hyW
  have hback := hy.map e.holomorphic_invFun hr1
  simp only [Homeomorph.symm_apply_apply] at hback
  have hout := hback.mono hWU
  simpa only [f,dite_eq_left hyW,xW] using hout

theorem disc_peak_ratio {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1)
    {a b : ℂ} (ha : ‖a‖ < 1/8) (hb : ‖b‖ < 1/8) :
    ‖1-f b‖ ≤ 3*‖1-f a‖ := by
  have hmaps : MapsTo (fun z : ℂ => a+z) (ball 0 (1/2)) (ball 0 1) := by
    intro z hz
    rw [mem_ball,dist_zero_right] at hz ⊢
    exact (norm_add_le a z).trans_lt (by linarith)
  let g : ℂ → ℂ := fun z => f (a+z)-f a
  have hg : DifferentiableOn ℂ g (ball 0 (1/2)) :=
    (hf.comp (by fun_prop) hmaps).sub_const _
  have hba : ‖b-a‖ < 1/4 := (norm_sub_le b a).trans_lt (by linarith)
  have hz : b-a ∈ ball (0 : ℂ) (1/2) := by
    rw [mem_ball,dist_zero_right]; linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let M : ℝ := ‖1-f a‖ + ε/2
  have hM : 0 < M := by dsimp [M]; positivity
  have hgre : MapsTo g (ball 0 (1/2)) {z | z.re ≤ M} := by
    intro z hz
    have hRe : (f (a+z)).re ≤ 1 := (Complex.re_le_norm _).trans (hbound _ (hmaps hz))
    have hRea : 1 - (f a).re ≤ ‖1-f a‖ := by simpa using Complex.re_le_norm (1-f a)
    change (f (a+z)-f a).re ≤ M
    rw [Complex.sub_re]
    dsimp [M]
    linarith
  have hbc := Complex.borelCaratheodory_zero hM hg hgre (by norm_num) hz
    (by simp [g])
  have hden : 0 < 1/2-‖b-a‖ := by linarith
  have hbc' : ‖f b-f a‖ ≤ 2*M := by
    have htranslate : a + (b - a) = b := by ring
    simp only [g,htranslate] at hbc
    apply hbc.trans
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    ‖1-f b‖ ≤ ‖1-f a‖ + ‖f a-f b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖1-f a‖ + 2*M := by rw [norm_sub_rev (f a) (f b)]; exact add_le_add (le_refl _) hbc'
    _ = 3*‖1-f a‖ + ε := by dsimp [M]; ring

theorem DiscRelation.entire_peak_ratio {n : ℕ} {U : Set (Affine n)}
    {g : Affine n → ℂ} (hg : Differentiable ℂ g)
    (hbound : ∀ z ∈ U, ‖g z‖ ≤ 1) {x y : U}
    (hxy : DiscRelation U (1/8) x y) :
    ‖1-g y.val‖ ≤ 3*‖1-g x.val‖ := by
  obtain ⟨f,hf,hU,a,b,ha,hb,hax,hby⟩ := hxy
  have he := disc_peak_ratio (hg.comp_differentiableOn hf) (fun z hz => hbound _ (hU hz)) ha hb
  simpa only [Function.comp_apply,hax,hby] using he

theorem RelationSteps.symm {X : Type*} {R : X → X → Prop}
    (hsym : ∀ x y, R x y → R y x) {j : ℕ} {x y : X}
    (h : RelationSteps R j x y) : RelationSteps R j y x := by
  induction j generalizing x y with
  | zero => exact Eq.symm h
  | succ j ih =>
      rcases h with h | ⟨z,hxz,hzy⟩
      · exact Or.inl (ih h)
      · simpa only [Nat.add_comm 1 j] using
          (RelationSteps.single (hsym z y hzy)).trans (ih hxz)

theorem RelationSteps.map {X Y : Type*} {R : X → X → Prop} {S : Y → Y → Prop}
    {f : X → Y} (hf : ∀ x y, R x y → S (f x) (f y)) {j : ℕ} {x y : X}
    (h : RelationSteps R j x y) : RelationSteps S j (f x) (f y) := by
  induction j generalizing y with
  | zero => exact congrArg f h
  | succ j ih =>
      rcases h with h | ⟨z,hxz,hzy⟩
      · exact Or.inl (ih h)
      · exact Or.inr ⟨f z,ih hxz,hf z y hzy⟩

theorem RelationSteps.ratio {X : Type*} {R : X → X → Prop} {v : X → ℝ}
    (hv : ∀ x, 0 ≤ v x) {c : ℝ} (hc : 1 ≤ c)
    (hR : ∀ x y, R x y → v y ≤ c*v x) {j : ℕ} {x y : X}
    (h : RelationSteps R j x y) : v y ≤ c^j*v x := by
  induction j generalizing y with
  | zero =>
      change x = y at h
      subst y
      simp
  | succ j ih =>
      have hc0 : 0 ≤ c := le_trans zero_le_one hc
      rcases h with h | ⟨z,hxz,hzy⟩
      · calc
          v y ≤ c^j*v x := ih h
          _ ≤ c^(j+1)*v x := mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hc (Nat.le_succ _)) (hv x)
      · calc
          v y ≤ c*v z := hR z y hzy
          _ ≤ c*(c^j*v x) := mul_le_mul_of_nonneg_left (ih hxz) hc0
          _ = c^(j+1)*v x := by rw [pow_succ]; ring

theorem IsSmooth.compact_disc_chains {n : ℕ} {U : Set (Affine n)}
    [Nonempty U] [PreconnectedSpace U] (hU : IsSmooth U)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {K E : Set U} (hK : IsCompact K) (hE : IsCompact E) :
    ∃ N : ℕ, ∀ k ∈ K, ∀ q ∈ E, RelationSteps (DiscRelation U r) N k q := by
  let x : U := Classical.choice inferInstance
  obtain ⟨N,hN⟩ := compact_connected_relation_chains (DiscRelation U r)
    (fun _ _ h => discRelation_symm h) (hU.discRelation_nhds hr hr1) x (hK.union hE)
  refine ⟨N+N,?_⟩
  intro k hk q hq
  exact ((hN k (Or.inl hk)).symm (fun _ _ h => discRelation_symm h)).trans
    (hN q (Or.inr hq))

theorem IsSmooth.compact_peak_ratio {n : ℕ} {U : Set (Affine n)}
    [Nonempty U] [PreconnectedSpace U] (hU : IsSmooth U)
    {K E : Set U} (hK : IsCompact K) (hE : IsCompact E) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Affine n → ℂ, Differentiable ℂ g →
      (∀ z ∈ U, ‖g z‖ ≤ 1) → ∀ f : U → U,
      HolomorphicOnSubset U (fun z => (f z).val) →
      ∀ k ∈ K, ∀ q ∈ E, ‖1-g (f q).val‖ ≤ C*‖1-g (f k).val‖ := by
  obtain ⟨N,hN⟩ := hU.compact_disc_chains (by norm_num : 0 < (1:ℝ)/8)
    (by norm_num : (1:ℝ)/8 ≤ 1) hK hE
  refine ⟨3^N,by positivity,?_⟩
  intro g hg hb f hf k hk q hq
  have hchain := (hN k hk q hq).map
    (fun _ _ h => h.map hf (by norm_num : (1:ℝ)/8 ≤ 1))
  exact hchain.ratio (fun _ => norm_nonneg _) (by norm_num : (1:ℝ) ≤ 3)
    (fun _ _ h => h.entire_peak_ratio hg hb)

end Release061

end OAI
