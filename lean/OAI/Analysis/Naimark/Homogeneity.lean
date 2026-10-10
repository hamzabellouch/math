import OAI.Analysis.Naimark.Stages

namespace OAI

noncomputable section

namespace NaimarkZFC

open Filter Topology
open scoped InnerProductSpace
namespace KOS

section

variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

def Close (F : Finset A) (ε : ℝ) (f g : A →L[ℂ] ℂ) : Prop :=
  ∀ a ∈ F, dist (f a) (g a) < ε

omit partialOrderA starOrderedRingA in
theorem Close.symm [PartialOrder A] [StarOrderedRing A] {F : Finset A} {ε : ℝ} {f g : A →L[ℂ] ℂ}
    (h : Close F ε f g) : Close F ε g f := by
  intro a ha
  rw [dist_comm]
  exact h a ha

def LocalControl : Prop :=
  ∀ (f : A →L[ℂ] ℂ), IsPureState f → ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (G : Finset A) (δ : ℝ), 0 < δ ∧
      ∀ (g : A →L[ℂ] ℂ), IsPureState g → Close G δ f g →
        ∀ (K : Finset A) (η : ℝ), 0 < η →
          ∃ θ : A ≃⋆ₐ[ℂ] A,
            (∀ a ∈ F, dist (θ a) a < ε) ∧
            Close K η (restrictState θ.toStarAlgHom f) g

def SameClassControl : Prop :=
  ∀ (f : A →L[ℂ] ℂ) (hf : IsPureState f), ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (G : Finset A) (δ : ℝ), 0 < δ ∧
      ∀ (g : A →L[ℂ] ℂ) (hg : IsPureState g),
        PureStateEquivalent f hf g hg → Close G δ f g →
          ∃ θ : A ≃⋆ₐ[ℂ] A,
            (∀ a ∈ F, dist (θ a) a < ε) ∧
            restrictState θ.toStarAlgHom f = g

theorem inner_fitting (hA : IsSimpleCStar A) (f g : A →L[ℂ] ℂ)
    (hf : IsPureState f) (hg : IsPureState g)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary A,
      Close F ε (restrictState (Unitary.conjStarAlgAut ℂ A u).symm.toStarAlgHom f) g := by
  let P := positiveOfSquares f hf.1.2
  let π := P.gnsNonUnitalStarAlgHom
  let ξ := gnsVector P
  obtain ⟨u,hu⟩ := simple_pure_inner_orbit_finite hA π
    (pure_gns_irreducible f hf.1 hf) ξ
    (gnsVector_norm_eq_one P ((isState_iff f).mp hf.1).1) g hg F ε hε
  refine ⟨u,fun a ha => ?_⟩
  rw [dist_eq_norm]
  change ‖f (star (u:A)*a*(u:A)) - g a‖ < ε
  change ‖P (star (u:A)*a*(u:A)) - g a‖ < ε
  rw [← gnsVector_coefficient P]
  exact hu a ha

theorem localControl_of_sameClassControl (hA : IsSimpleCStar A)
    (h : SameClassControl (A := A)) : LocalControl (A := A) := by
  classical
  intro f hf F ε hε
  obtain ⟨G,δ,hδ,hG⟩ := h f hf F ε hε
  refine ⟨G,δ/3,by positivity,?_⟩
  intro g hg hfg K η hη
  obtain ⟨u,hu⟩ := inner_fitting hA f g hf hg (G ∪ K)
    (min η (δ/3)) (lt_min hη (by positivity))
  let e := (Unitary.conjStarAlgAut ℂ A u).symm
  let p := restrictState e.toStarAlgHom f
  have hp : IsPureState p := isPureState_restrict_equiv e f hf
  have heq : PureStateEquivalent f hf p hp :=
    pureState_equivalent_of_conjugate f p hf hp u (fun _ => rfl)
  have hfp : Close G δ f p := by
    intro a ha
    have h₁ := hfg a ha
    have h₂ := (hu a (Finset.mem_union_left K ha)).trans_le (min_le_right _ _)
    have ht := dist_triangle (f a) (g a) (p a)
    rw [dist_comm (g a) (p a)] at ht
    linarith
  obtain ⟨θ,hθ,hpθ⟩ := hG p hp heq hfp
  refine ⟨θ,hθ,?_⟩
  rw [hpθ]
  intro a ha
  exact (hu a (Finset.mem_union_right G ha)).trans_le (min_le_left _ _)

end

section
open Filter Topology
variable {A : Type*} [cStarAlgebraA : CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

structure ControlData (f : A →L[ℂ] ℂ) (F : Finset A) (ε : ℝ) where
  tests : Finset A
  radius : ℝ
  positive : 0 < radius
  correct : ∀ (g : A →L[ℂ] ℂ), IsPureState g → Close tests radius f g →
    ∀ (K : Finset A) (η : ℝ), 0 < η →
      ∃ θ : A ≃⋆ₐ[ℂ] A,
        (∀ a ∈ F, dist (θ a) a < ε) ∧
        Close K η (restrictState θ.toStarAlgHom f) g

omit partialOrderA starOrderedRingA in
theorem exists_controlData [PartialOrder A] [StarOrderedRing A] (h : LocalControl (A := A))
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (F : Finset A) (ε : ℝ) (hε : 0 < ε)
    (T : Finset A) (r : ℝ) (hr : 0 < r) :
    ∃ C : ControlData f F ε, T ⊆ C.tests ∧ C.radius ≤ r := by
  classical
  obtain ⟨G,δ,hδ,hC⟩ := h f hf F ε hε
  refine ⟨⟨G ∪ T,min δ r,lt_min hδ hr,?_⟩,Finset.subset_union_right, min_le_right _ _⟩
  intro g hg hgclose K η hη
  apply hC g hg _ K η hη
  intro a ha
  exact (hgclose a (Finset.mem_union_left T ha)).trans_le (min_le_left _ _)

def tests (q : ℕ → A) (n : ℕ) : Finset A := by
  classical
  exact (Finset.range (n+1)).image q

omit cStarAlgebraA partialOrderA starOrderedRingA in
theorem mem_tests [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (q : ℕ → A) {k n : ℕ} (hk : k ≤ n) : q k ∈ tests q n := by
  classical
  exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (Nat.lt_succ_of_le hk),rfl⟩

def orbitTests (q : ℕ → A) (α : A ≃⋆ₐ[ℂ] A) (n : ℕ) : Finset A := by
  classical
  exact tests q n ∪ (tests q n).image α.symm

theorem step_control (q : ℕ → A) (α θ : A ≃⋆ₐ[ℂ] A) (n : ℕ) (ε : ℝ)
    (hθ : ∀ a ∈ orbitTests q α n, dist (θ a) a < ε) {k : ℕ} (hk : k ≤ n) :
    dist (α (q k)) ((θ.trans α) (q k)) < ε ∧
      dist (α.symm (q k)) ((θ.trans α).symm (q k)) < ε := by
  classical
  have hq := mem_tests q hk
  constructor
  · change dist (α (q k)) (α (θ (q k))) < ε
    rw [(StarAlgEquiv.isometry α).dist_eq,dist_comm]
    exact hθ _ (Finset.mem_union_left _ hq)
  · change dist (α.symm (q k)) (θ.symm (α.symm (q k))) < ε
    rw [← (StarAlgEquiv.isometry θ).dist_eq (α.symm (q k))
      (θ.symm (α.symm (q k))), θ.apply_symm_apply]
    apply hθ
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q k,hq,rfl⟩)

omit partialOrderA starOrderedRingA in
@[simp] theorem restrict_trans [PartialOrder A] [StarOrderedRing A] (α θ : A ≃⋆ₐ[ℂ] A) (f : A →L[ℂ] ℂ) :
    restrictState (θ.trans α).toStarAlgHom f =
      restrictState θ.toStarAlgHom (restrictState α.toStarAlgHom f) := by
  ext a
  rfl

def data (h : LocalControl (A := A)) (q : ℕ → A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (α : A ≃⋆ₐ[ℂ] A) (n : ℕ) :
    ControlData (restrictState α.toStarAlgHom f) (orbitTests q α n) ((1/2:ℝ)^n) :=
  Classical.choose (exists_controlData h _ (isPureState_restrict_equiv α f hf)
    (orbitTests q α n) ((1/2:ℝ)^n) (pow_pos (by norm_num) _) (tests q n)
    ((1/2:ℝ)^n) (pow_pos (by norm_num) _))

theorem data_tests (h : LocalControl (A := A)) (q : ℕ → A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (α : A ≃⋆ₐ[ℂ] A) (n : ℕ) :
    tests q n ⊆ (data h q f hf α n).tests :=
  (Classical.choose_spec (exists_controlData h _ (isPureState_restrict_equiv α f hf)
    (orbitTests q α n) ((1/2:ℝ)^n) (pow_pos (by norm_num) _) (tests q n)
    ((1/2:ℝ)^n) (pow_pos (by norm_num) _))).1

theorem data_radius (h : LocalControl (A := A)) (q : ℕ → A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (α : A ≃⋆ₐ[ℂ] A) (n : ℕ) :
    (data h q f hf α n).radius ≤ (1/2:ℝ)^n :=
  (Classical.choose_spec (exists_controlData h _ (isPureState_restrict_equiv α f hf)
    (orbitTests q α n) ((1/2:ℝ)^n) (pow_pos (by norm_num) _) (tests q n)
    ((1/2:ℝ)^n) (pow_pos (by norm_num) _))).2

variable (h : LocalControl (A := A)) (q : ℕ → A)
  (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)

structure Stage (n : ℕ) where
  left : A ≃⋆ₐ[ℂ] A
  right : A ≃⋆ₐ[ℂ] A
  close : Close (data h q f hf left n).tests (data h q f hf left n).radius
    (restrictState left.toStarAlgHom f) (restrictState right.toStarAlgHom g)

def Step {n : ℕ} (s : Stage h q f g hf n) (t : Stage h q f g hf (n+1)) : Prop :=
  ∀ k ≤ n,
    dist (s.left (q k)) (t.left (q k)) ≤ (1/2:ℝ)^n ∧
    dist (s.left.symm (q k)) (t.left.symm (q k)) ≤ (1/2:ℝ)^n ∧
    dist (s.right (q k)) (t.right (q k)) ≤ (1/2:ℝ)^n ∧
    dist (s.right.symm (q k)) (t.right.symm (q k)) ≤ (1/2:ℝ)^n

include hg in

theorem exists_next {n : ℕ} (s : Stage h q f g hf n) :
    ∃ t : Stage h q f g hf (n+1), Step h q f g hf s t := by
  let R := data h q g hg s.right n
  obtain ⟨θ,hθ,hmatch⟩ := (data h q f hf s.left n).correct _
    (isPureState_restrict_equiv s.right g hg) s.close R.tests R.radius R.positive
  let α := θ.trans s.left
  have hmatch' : Close R.tests R.radius
      (restrictState s.right.toStarAlgHom g) (restrictState α.toStarAlgHom f) := by
    simpa only [α,restrict_trans] using hmatch.symm
  let L := data h q f hf α (n+1)
  obtain ⟨ψ,hψ,hmatch₂⟩ := R.correct _ (isPureState_restrict_equiv α f hf)
    hmatch' L.tests L.radius L.positive
  let β := ψ.trans s.right
  have hnew : Close L.tests L.radius
      (restrictState α.toStarAlgHom f) (restrictState β.toStarAlgHom g) := by
    simpa only [β,restrict_trans] using hmatch₂.symm
  refine ⟨⟨α,β,hnew⟩,fun k hk => ?_⟩
  have h₁ := step_control q s.left θ n _ hθ hk
  have h₂ := step_control q s.right ψ n _ hψ hk
  exact ⟨h₁.1.le,h₁.2.le,h₂.1.le,h₂.2.le⟩

include hg in

theorem exists_initial (hA : IsSimpleCStar A) : Nonempty (Stage h q f g hf 0) := by
  let α : A ≃⋆ₐ[ℂ] A := StarAlgEquiv.refl ℂ A
  let L := data h q f hf α 0
  obtain ⟨u,hu⟩ := inner_fitting hA g (restrictState α.toStarAlgHom f) hg
    (isPureState_restrict_equiv α f hf) L.tests L.radius L.positive
  exact ⟨⟨α,(Unitary.conjStarAlgAut ℂ A u).symm,hu.symm⟩⟩

end

section
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_controlled_pair (h : LocalControl (A := A)) (hA : IsSimpleCStar A)
    (q : ℕ → A) (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    ∃ α β : ℕ → A ≃⋆ₐ[ℂ] A, ∀ n k, k ≤ n →
      dist (α n (q k)) (α (n+1) (q k)) ≤ (1/2:ℝ)^n ∧
      dist ((α n).symm (q k)) ((α (n+1)).symm (q k)) ≤ (1/2:ℝ)^n ∧
      dist (β n (q k)) (β (n+1) (q k)) ≤ (1/2:ℝ)^n ∧
      dist ((β n).symm (q k)) ((β (n+1)).symm (q k)) ≤ (1/2:ℝ)^n ∧
      dist (f (α n (q k))) (g (β n (q k))) ≤ (1/2:ℝ)^n := by
  let s₀ := Classical.choice (exists_initial h q f g hf hg hA)
  let next := fun (n : ℕ) (s : Stage h q f g hf n) =>
    Classical.choose (exists_next h q f g hf hg s)
  let s : (n : ℕ) → Stage h q f g hf n := fun n => Nat.rec s₀ next n
  refine ⟨fun n => (s n).left,fun n => (s n).right,fun n k hk => ?_⟩
  have hstep : Step h q f g hf (s n) (s (n+1)) :=
    Classical.choose_spec (exists_next h q f g hf hg (s n))
  obtain ⟨h₁,h₂,h₃,h₄⟩ := hstep k hk
  refine ⟨h₁,h₂,h₃,h₄,?_⟩
  exact ((s n).close _ (data_tests h q f hf _ n (mem_tests q hk))).le.trans
    (data_radius h q f hf _ n)

theorem cauchy_of_geometric_tests (q : ℕ → A) (hq : DenseRange q)
    (α : ℕ → A ≃⋆ₐ[ℂ] A)
    (h : ∀ n k, k ≤ n → dist (α n (q k)) (α (n+1) (q k)) ≤ (1/2:ℝ)^n)
    (a : A) : CauchySeq (fun n => α n a) := by
  apply isometry_cauchy_on_dense (fun n a => α n a)
    (fun n => StarAlgEquiv.isometry (α n)) (Set.range q) hq _ a
  rintro b ⟨k,rfl⟩
  exact cauchySeq_of_tail_geometric_steps _ k (fun n hn => h n k hn)

theorem homogeneity_of_localControl [TopologicalSpace.SeparableSpace A]
    (h : LocalControl (A := A)) (hA : IsSimpleCStar A)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    ∃ γ : A ≃⋆ₐ[ℂ] A, ∀ a, f (γ a) = g a := by
  obtain ⟨q,hq⟩ := TopologicalSpace.exists_dense_seq A
  obtain ⟨α,β,H⟩ := exists_controlled_pair h hA q f g hf hg
  have hα := cauchy_of_geometric_tests q hq α (fun n k hk => (H n k hk).1)
  have hαi := cauchy_of_geometric_tests q hq (fun n => (α n).symm)
    (fun n k hk => (H n k hk).2.1)
  have hβ := cauchy_of_geometric_tests q hq β (fun n k hk => (H n k hk).2.2.1)
  have hβi := cauchy_of_geometric_tests q hq (fun n => (β n).symm)
    (fun n k hk => (H n k hk).2.2.2.1)
  let alphaLimit := autLimitEquiv α hα hαi
  let betaLimit := autLimitEquiv β hβ hβi
  have hvalues (k : ℕ) : f (alphaLimit (q k)) = g (betaLimit (q k)) := by
    have hz : Tendsto (fun n => dist (f (α n (q k))) (g (β n (q k))))
        atTop (𝓝 0) := by
      exact squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
        (eventually_atTop.mpr ⟨k,fun n hn => (H n k hn).2.2.2.2⟩)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have h₁ : Tendsto (fun n => f (α n (q k))) atTop (𝓝 (f (alphaLimit (q k)))) :=
      f.continuous.tendsto _ |>.comp (tendsto_autPointwiseLimit α hα (q k))
    have h₂ : Tendsto (fun n => g (β n (q k))) atTop (𝓝 (g (betaLimit (q k)))) :=
      g.continuous.tendsto _ |>.comp (tendsto_autPointwiseLimit β hβ (q k))
    exact dist_eq_zero.mp (tendsto_nhds_unique (h₁.dist h₂) hz)
  have he : (fun a => f (alphaLimit a)) = fun a => g (betaLimit a) := by
    apply hq.equalizer (f.continuous.comp (StarAlgEquiv.isometry alphaLimit).continuous)
      (g.continuous.comp (StarAlgEquiv.isometry betaLimit).continuous)
    funext k
    exact hvalues k
  refine ⟨betaLimit.symm.trans alphaLimit,fun a => ?_⟩
  have hh := congrFun he (betaLimit.symm a)
  simpa only [StarAlgEquiv.trans_apply,betaLimit.apply_symm_apply] using hh

theorem homogeneity_of_sameClassControl [TopologicalSpace.SeparableSpace A]
    (h : SameClassControl (A := A)) (hA : IsSimpleCStar A)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    ∃ γ : A ≃⋆ₐ[ℂ] A, ∀ a, f (γ a) = g a :=
  homogeneity_of_localControl (localControl_of_sameClassControl hA h) hA f g hf hg

end

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

def NearCentralRows : Prop :=
  ∀ (f : A →L[ℂ] ℂ) (hf : IsPureState f) (F : Finset A) (c : ℝ), 0 < c →
    ∃ (n : ℕ) (x : Fin n → A),
      pureGNS f hf (rowAverage x 1) (gnsVector (positiveOfSquares f hf.1.2)) =
        gnsVector (positiveOfSquares f hf.1.2) ∧
      ∀ b ∈ F, ∀ a : A, 0 ≤ a → a ≤ 1 →
        ‖b*rowAverage x a-rowAverage x a*b‖ ≤ c

omit partialOrderA starOrderedRingA in
lemma norm_inverse_inner_displacement [PartialOrder A] [StarOrderedRing A] (u : unitary A) (a : A) :
    dist ((Unitary.conjStarAlgAut ℂ A u).symm a) a = ‖a*(u:A)-(u:A)*a‖ := by
  rw [dist_eq_norm,Unitary.conjStarAlgAut_symm_apply]
  have he : star (u:A)*a*(u:A)-a = star (u:A)*(a*(u:A)-(u:A)*a) := by
    rw [mul_sub,← mul_assoc (star (u:A)) (u:A),u.property.1,one_mul,mul_assoc]
  rw [he]
  exact CStarRing.norm_coe_unitary_mul (star u) _

theorem sameClassControl_of_nearCentralRows (hA : IsSimpleCStar A)
    (hinf : ¬ FiniteDimensional ℂ A) (hrow : NearCentralRows (A := A)) :
    SameClassControl (A := A) := by
  classical
  intro f hf F ε hε
  let P := positiveOfSquares f hf.1.2
  let π := pureGNS f hf
  let ξ := gnsVector P
  have hπ : IsIrreducible π := pure_gns_irreducible f hf.1 hf
  have hi : Function.Injective π := simple_nonzeroStarHom_injective hA π hπ.1
  have hno : ∀ a : A, IsCompactOperator (π a) → π a = 0 :=
    simple_infinite_no_compacts hA hinf π hπ
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one P ((isState_iff f).mp hf.1).1
  have hcoeff (a : A) : vectorFunctional π ξ a = f a := gnsVector_coefficient P a
  let B : ℝ := ∑ b ∈ F, ‖b‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let r : ℝ := min 1 (ε/(1536*(B+1)))
  have hr : 0 < r := lt_min (by norm_num) (div_pos hε (by positivity))
  have hr1 : r ≤ 1 := min_le_left _ _
  obtain ⟨n,x,hfix,hcentral⟩ := hrow f hf F (ε/32) (by positivity)
  obtain ⟨δ,hδ,hmatch⟩ := row_controlled_matching π hπ hi hno x ξ hξ hfix
    F (ε/32) hcentral r hr hr1
  refine ⟨rowFrameTests x,δ,hδ,fun g hg he hclose => ?_⟩
  obtain ⟨η,hη,hηcoeff⟩ := equivalent_pure_coefficient_vector
    (StarAlgHom.id ℂ A) f g hf hg he π ξ hcoeff
  change ∀ a : A, ⟪η,π a η⟫_ℂ = g a at hηcoeff
  have hcl (a : A) (ha : a ∈ rowFrameTests x) :
      ‖vectorFunctional π ξ a-vectorFunctional π η a‖ < δ := by
    rw [hcoeff]
    change ‖f a-⟪η,π a η⟫_ℂ‖ < δ
    rw [hηcoeff]
    simpa only [dist_eq_norm] using hclose a ha
  obtain ⟨u,hu,hcomm⟩ := hmatch η hη hcl
  refine ⟨(Unitary.conjStarAlgAut ℂ A u).symm,fun a ha => ?_,?_⟩
  · rw [norm_inverse_inner_displacement]
    have haB : ‖a‖ ≤ B := Finset.single_le_sum (fun b _ => norm_nonneg b) ha
    have hr' : r ≤ ε/(1536*(B+1)) := min_le_right _ _
    have hrB : r*(1536*(B+1)) ≤ ε := (le_div_iff₀ (by positivity)).mp hr'
    have hb : 384*‖a‖*r ≤ ε/4 := by nlinarith [mul_le_mul_of_nonneg_right haB hr.le]
    exact (hcomm a ha).trans_lt (by linarith)
  · ext a
    change f (star (u:A)*a*(u:A)) = g a
    rw [← hcoeff]
    change ⟪ξ,π (star (u:A)*a*(u:A)) ξ⟫_ℂ = g a
    simp only [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
    rw [hu]
    exact hηcoeff a

theorem homogeneity_of_nearCentralRows [TopologicalSpace.SeparableSpace A]
    (hA : IsSimpleCStar A) (hinf : ¬ FiniteDimensional ℂ A)
    (hrow : NearCentralRows (A := A))
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    ∃ γ : A ≃⋆ₐ[ℂ] A, ∀ a, f (γ a) = g a :=
  homogeneity_of_sameClassControl (sameClassControl_of_nearCentralRows hA hinf hrow)
    hA f g hf hg

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]

lemma rowAverage_norm (x : ι → A) (a : A) :
    ‖rowAverage x a‖ ≤ (∑ i, ‖x i‖^2)*‖a‖ := by
  calc
    _ ≤ ∑ i, ‖x i*a*star (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x i‖^2*‖a‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ (‖x i‖*‖a‖)*‖star (x i)‖ := (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ = _ := by rw [norm_star]; ring
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma rowAverage_congruence (x : ι → A) (b a : A) :
    rowAverage (fun i => b*x i) a = b*rowAverage x a*star b := by
  simp only [rowAverage,star_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]

lemma near_congruence_norm (b y : A) (d : ℝ) (hd : ‖b-1‖ ≤ d) (hd1 : d ≤ 1) :
    ‖b*y*star b-y‖ ≤ 3*d*‖y‖ := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hb : ‖b‖ ≤ 1+d := by
    have h := norm_add_le (1:A) (b-1)
    rw [add_sub_cancel] at h
    have h1 : ‖(1:A)‖ ≤ 1 := by
      nontriviality A
      simp
    linarith
  have he : b*y*star b-y = (b-1)*y*star b+y*star (b-1) := by
    simp only [star_sub,star_one]
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(b-1)*y*star b‖+‖y*star (b-1)‖ := norm_add_le _ _
    _ ≤ (d*‖y‖)*(1+d)+‖y‖*d := by
      apply add_le_add
      · exact (norm_mul_le _ _).trans (mul_le_mul
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _)))
          (by simpa using hb) (norm_nonneg _) (by positivity))
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
          (by simpa only [norm_star] using hd) (norm_nonneg _))
    _ ≤ 3*d*‖y‖ := by nlinarith [mul_nonneg (mul_nonneg hd0 (norm_nonneg y)) (sub_nonneg.mpr hd1)]

lemma commutator_congruence_norm (F b y : A) (d c : ℝ)
    (hd : ‖b-1‖ ≤ d) (hd1 : d ≤ 1) (hy : ‖y‖ ≤ 1)
    (hc : ‖F*y-y*F‖ ≤ c) :
    ‖F*(b*y*star b)-(b*y*star b)*F‖ ≤ c+6*‖F‖*d := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hn : ‖b*y*star b-y‖ ≤ 3*d :=
    (near_congruence_norm b y d hd hd1).trans (by nlinarith)
  have he : F*(b*y*star b)-(b*y*star b)*F =
      (F*y-y*F) + F*(b*y*star b-y)-(b*y*star b-y)*F := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖F*y-y*F‖+‖F*(b*y*star b-y)‖+‖(b*y*star b-y)*F‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ c+‖F‖*(3*d)+(3*d)*‖F‖ := by
      apply add_le_add
      · exact add_le_add hc ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _)))
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    _ = _ := by ring

variable [PartialOrder A] [StarOrderedRing A]

def ApproxNearCentralRows : Prop :=
  ∀ (f : A →L[ℂ] ℂ) (hf : IsPureState f) (F : Finset A) (c : ℝ), 0 < c →
    ∃ (n : ℕ) (x : Fin n → A), (∑ i, ‖x i‖^2) ≤ 1 ∧
      ‖pureGNS f hf (rowAverage x 1) (gnsVector (positiveOfSquares f hf.1.2)) -
        gnsVector (positiveOfSquares f hf.1.2)‖ ≤ c ∧
      ∀ b ∈ F, ∀ a : A, 0 ≤ a → a ≤ 1 →
        ‖b*rowAverage x a-rowAverage x a*b‖ ≤ c

theorem nearCentralRows_of_approx (h : ApproxNearCentralRows (A := A)) :
    NearCentralRows (A := A) := by
  classical
  intro f hf F c hc
  let B : ℝ := ∑ z ∈ F, ‖z‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let t : ℝ := min (1/48) (c/(1+288*B))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hc (by positivity))
  have ht48 : t ≤ 1/48 := min_le_left _ _
  have htc : t*(1+288*B) ≤ c :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨n,x,hx,hfix,hcentral⟩ := h f hf F t ht
  let π := pureGNS f hf
  let ξ := gnsVector (positiveOfSquares f hf.1.2)
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one _ ((isState_iff f).mp hf.1).1
  obtain ⟨b,hb,hbfix⟩ := irreducible_near_congruence π
    (pure_gns_irreducible f hf.1 hf) (rowAverage x 1)
    (rowAverage_selfAdjoint x 1 (IsSelfAdjoint.one A)) ξ hξ t hfix (by linarith)
  refine ⟨n,fun i => b*x i,?_,?_⟩
  · simpa only [rowAverage_congruence] using hbfix
  · intro z hz a ha ha1
    rw [rowAverage_congruence]
    have hay : ‖rowAverage x a‖ ≤ 1 := by
      have han : ‖a‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg a ha).mpr ha1
      exact (rowAverage_norm x a).trans (by nlinarith [norm_nonneg a])
    have hzB : ‖z‖ ≤ B := Finset.single_le_sum (fun z _ => norm_nonneg z) hz
    exact (commutator_congruence_norm z b (rowAverage x a) (48*t) t hb
      (by linarith) hay (hcentral z hz a ha ha1)).trans (by
        nlinarith [mul_le_mul_of_nonneg_right hzB ht.le])

theorem homogeneity_of_approxRows [TopologicalSpace.SeparableSpace A]
    (hA : IsSimpleCStar A) (hinf : ¬ FiniteDimensional ℂ A)
    (h : ApproxNearCentralRows (A := A))
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    ∃ γ : A ≃⋆ₐ[ℂ] A, ∀ a, f (γ a) = g a :=
  homogeneity_of_nearCentralRows hA hinf (nearCentralRows_of_approx h) f g hf hg

end KOS

open scoped CStarAlgebra ComplexOrder
namespace TracialStage

variable (X : TracialStage) {B : Type} [CStarAlgebra B]
  [partialOrderB : PartialOrder B] [starOrderedRingB : StarOrderedRing B] [topologicalSpaceSeparableSpaceB : TopologicalSpace.SeparableSpace B]
  (hB : IsSimpleCStar B) (ψ : CAR →⋆ₐ[ℂ] B) (φ : B →⋆ₐ[ℂ] X)
  (hφ : Function.Injective φ) (hbase : ∀ a, φ (ψ a) = X.base a)
  (hU : PureUEP φ) (f : X →L[ℂ] ℂ) (hf : IsPureState f)
  (hfr : IsPureState (restrictState φ f))
  (hrow : KOS.ApproxNearCentralRows (A := B))

include hbase in
omit partialOrderB starOrderedRingB topologicalSpaceSeparableSpaceB in
lemma core_car_injective [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B] : Function.Injective ψ := by
  intro a b h
  apply X.base_injective
  rw [← hbase a,← hbase b,h]

include hbase in
lemma core_infinite : ¬ FiniteDimensional ℂ B := by
  intro h
  exact carInfiniteDimensional (Module.Finite.of_injective ψ.toLinearMap
    (core_car_injective X ψ φ hbase))

include hbase in
omit partialOrderB starOrderedRingB topologicalSpaceSeparableSpaceB in
lemma core_reference_peaks [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B] : Peaks (fun n => φ (ψ (carPeak n))) X.reference := by
  simpa only [hbase] using X.reference_peaks

include hB hφ hbase hU hf hfr hrow in

theorem exists_supported_peak_pair :
    ∃ Q : PeakingPairData X,
      (∀ a, Q.trace a = X.trace a) ∧ Q.state false = X.reference ∧
      Q.state true = f ∧ (∀ n, Q.peak false n = X.base (carPeak n)) ∧
      (∀ i n, Q.peak i n ∈ Set.range φ) := by
  have hp := core_reference_peaks X ψ φ hbase
  have hpr := (hp.restrict φ hφ).1.isPureState
  obtain ⟨γ,hγ⟩ := KOS.homogeneity_of_approxRows hB
    (core_infinite X ψ φ hbase) hrow (restrictState φ f)
    (restrictState φ X.reference) hfr hpr
  have he : restrictState γ.toStarAlgHom (restrictState φ f) =
      restrictState φ X.reference := by
    ext a
    exact hγ a
  let Q := homogeneousCARPeakPair ψ φ hφ X.reference f hp hfr hf.1 hU γ he
    X.positiveTrace X.tracial X.positiveTrace_normalized X.positiveTrace_faithful
  refine ⟨Q,fun _ => rfl,rfl,rfl,fun n => hbase _,?_⟩
  intro i n
  cases i
  · exact ⟨ψ (carPeak n),rfl⟩
  · exact ⟨γ (ψ (carPeak n)),rfl⟩

include hB hφ hbase hU hf hfr hrow in

theorem exists_joining_successor :
    ∃ Y : TracialStage, ∃ j : Hom X Y,
      ∃ F : Y →L[ℂ] ℂ, ∃ hF : IsPureState F,
        restrictState j.map F = f ∧
        PureStateEquivalent Y.reference Y.reference_spec.1 F hF := by
  classical
  by_cases he : PureStateEquivalent X.reference X.reference_spec.1 f hf
  · exact ⟨X,Hom.id X,f,hf,rfl,he⟩
  · obtain ⟨Q,ht,h0,h1,_,_⟩ := exists_supported_peak_pair X hB ψ φ hφ hbase hU f hf hfr hrow
    have hne : ¬ PureStateEquivalent (Q.state false) (Q.peaks false).isPureState
        (Q.state true) (Q.peaks true).isPureState := by
      simpa only [h0,h1] using he
    let hs := Q.separated_of_inequivalent hne
    obtain ⟨F,hF,hr,hjoin⟩ := hnn_reference_join X Q hs ht f hf h0 h1
    exact ⟨hnn X Q hs,hnnHom X Q hs ht,F,hF,hr,hjoin⟩

end TracialStage

open Topology
section
variable {A C D ι : Type*} [CStarAlgebra A] [CStarAlgebra C] [CStarAlgebra D]

def starPair (a : A) : Bool → A
  | false => a
  | true => star a

@[simp] lemma starPair_false (a : A) : starPair a false = a := rfl
@[simp] lemma starPair_true (a : A) : starPair a true = star a := rfl
lemma star_starPair (a : A) (i : Bool) : star (starPair a i) = starPair a (!i) := by
  cases i <;> simp [starPair]

lemma map_hnnGenerated (φ : C →⋆ₐ[ℂ] D) (w : Bool → D) (ψ : D →⋆ₐ[ℂ] A)
    (hψ : Function.Injective ψ) :
    (hnnGenerated φ w).map ψ = hnnGenerated (ψ.comp φ) (fun i => ψ (w i)) := by
  have hcont := (NonUnitalStarAlgHom.isometry ψ hψ).continuous
  have hclosed := (NonUnitalStarAlgHom.isometry ψ hψ).isClosedEmbedding.isClosedMap
  rw [hnnGenerated,← StarSubalgebra.topologicalClosure_map _ ψ hclosed hcont,
    StarAlgHom.map_adjoin,hnnGenerated]
  congr 2
  rw [Set.image_union,← Set.range_comp,← Set.range_comp]
  rfl

lemma hnnGenerated_self (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (a : A) : hnnGenerated S.subtype (starPair a) =
      (StarAlgebra.adjoin ℂ ((S : Set A) ∪ {a})).topologicalClosure := by
  apply le_antisymm
  · apply StarSubalgebra.topologicalClosure_minimal _ isClosed_closure
    apply StarAlgebra.adjoin_le
    rintro x (⟨s,rfl⟩ | ⟨i,rfl⟩)
    · exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl s.property))
    · cases i
      · exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inr (Set.mem_singleton a)))
      · exact star_mem (subset_closure (StarAlgebra.subset_adjoin ℂ _
          (Or.inr (Set.mem_singleton a))))
  · apply StarSubalgebra.topologicalClosure_minimal _ (hnnGenerated_isClosed _ _)
    apply StarAlgebra.adjoin_le
    rintro x (hx | hx)
    · exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨⟨x,hx⟩,rfl⟩))
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨false,rfl⟩))

lemma generatedFamily_insert (base : Set A) (v : ι → A) (S : Set ι) (j : ι) :
    generatedFamily base v (insert j S) =
      (StarAlgebra.adjoin ℂ ((generatedFamily base v S : Set A) ∪ {v j})).topologicalClosure := by
  apply le_antisymm
  · apply StarSubalgebra.topologicalClosure_minimal _ isClosed_closure
    apply StarAlgebra.adjoin_le
    rintro x (hx | ⟨k,hk,rfl⟩)
    · exact subset_closure (StarAlgebra.subset_adjoin ℂ _
        (Or.inl (generatedFamily_contains_base base v S hx)))
    · rcases hk with rfl | hk
      · exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inr (Set.mem_singleton _)))
      · exact subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl (generatedFamily_contains base v hk)))
  · apply StarSubalgebra.topologicalClosure_minimal _ (generatedFamily_isClosed _ _ _)
    apply StarAlgebra.adjoin_le
    rintro x (hx | hx)
    · exact generatedFamily_mono base v (Set.subset_insert j S) hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact generatedFamily_contains base v (Set.mem_insert j S)

attribute [local instance] generatedFamily_isClosed

lemma hnnGenerated_eq_insert (base : Set A) (v : ι → A) (S : Set ι) (j : ι) :
    hnnGenerated (generatedFamily base v S).subtype (starPair (v j)) =
      generatedFamily base v (insert j S) := by
  rw [hnnGenerated_self,generatedFamily_insert]

end

open Topology

lemma StarAlgHom.equivClosedRange {B A : Type*} [CStarAlgebra B] [CStarAlgebra A]
    (φ : B →⋆ₐ[ℂ] A) (hφ : Function.Injective φ) (S : StarSubalgebra ℂ A)
    (hS : φ.range = S) :
    ∃ e : B ≃⋆ₐ[ℂ] S, ∀ b, (e b : A) = φ b := by
  let f : B →⋆ₐ[ℂ] S := φ.codRestrict S (fun b => by rw [← hS]; exact ⟨b,rfl⟩)
  have hfi : Function.Injective f := fun x y h => hφ (congrArg Subtype.val h)
  have hfs : Function.Surjective f := by
    intro y
    have hy : (y:A) ∈ φ.range := by rw [hS]; exact y.property
    obtain ⟨b,hb⟩ := hy
    exact ⟨b,Subtype.ext hb⟩
  exact ⟨StarAlgEquiv.ofBijective f ⟨hfi,hfs⟩,fun _ => rfl⟩

lemma StarAlgHom.range_comp_eq_map {A B C : Type*} [CStarAlgebra A]
    [CStarAlgebra B] [CStarAlgebra C] (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) :
    (ψ.comp φ).range = φ.range.map ψ := by
  ext c
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨φ a,⟨a,rfl⟩,rfl⟩
  · rintro ⟨b,⟨a,rfl⟩,rfl⟩
    exact ⟨a,rfl⟩

namespace PeakingPairData
variable {A B C : Type} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [CStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C]
  (D : PeakingPairData C) (φ : B →⋆ₐ[ℂ] C) (hφ : Function.Injective φ)
  (p : Bool → ℕ → B) (hp : ∀ i n, φ (p i n) = D.peak i n)
  (Ψ : D.HNNAlgebra →⋆ₐ[ℂ] A) (hΨ : Function.Injective Ψ)
  (ψ : B →⋆ₐ[ℂ] A) (w : Bool → A)
  (hbase : ∀ b, Ψ (D.hnnBase (φ b)) = ψ b)
  (hw : ∀ i, Ψ (D.hnnLetter i) = w i)

include hΨ hbase hw in

theorem inherited_ambient_presentation :
    ∃ e : (D.pullback φ hφ p hp).HNNAlgebra ≃⋆ₐ[ℂ] hnnGenerated ψ w,
      (∀ b, (e ((D.pullback φ hφ p hp).hnnBase b) : A) = ψ b) ∧
      (∀ i, (e ((D.pullback φ hφ p hp).hnnLetter i) : A) = w i) ∧
      (∀ g : A →L[ℂ] ℂ, (∀ b, g (Ψ b) = D.hnnTrace b) →
        ∀ b, g (e b) = (D.pullback φ hφ p hp).hnnTrace b) := by
  obtain ⟨F,hFi,hFb,hFw,hFt,hFr,_⟩ := D.pullback_hnn_inclusion φ hφ p hp
  have hcomp : Ψ.comp (D.hnnBase.comp φ) = ψ := by ext b; exact hbase b
  have hletter : (fun i => Ψ (D.hnnLetter i)) = w := funext hw
  have hr : (Ψ.comp F).range = hnnGenerated ψ w := by
    rw [StarAlgHom.range_comp_eq_map,hFr,map_hnnGenerated _ _ Ψ hΨ,hcomp,hletter]
  obtain ⟨e,he⟩ := StarAlgHom.equivClosedRange (Ψ.comp F) (hΨ.comp hFi) _ hr
  refine ⟨e,?_,?_,?_⟩
  · intro b
    rw [he]
    change Ψ (F ((D.pullback φ hφ p hp).hnnBase b)) = _
    rw [hFb,hbase]
  · intro i
    rw [he]
    change Ψ (F ((D.pullback φ hφ p hp).hnnLetter i)) = _
    rw [hFw,hw]
  · intro g hg b
    rw [he]
    exact (hg (F b)).trans (hFt b)

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData

section
local instance ambientSubalgebraOrder {A : Type} [CStarAlgebra A]
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] : PartialOrder S :=
  CStarAlgebra.spectralOrder S
local instance ambientSubalgebraStarOrder {A : Type} [CStarAlgebra A]
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] : StarOrderedRing S :=
  CStarAlgebra.spectralOrderedRing S
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (G : PeakingPairData A) (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
  (hp : ∀ i n, G.peak i n ∈ S)

def onSubalgebra : PeakingPairData S :=
  G.pullback S.subtype Subtype.val_injective (fun i n => ⟨G.peak i n,hp i n⟩)
    (fun _ _ => rfl)

@[simp] lemma onSubalgebra_peak (i : Bool) (n : ℕ) :
    ((G.onSubalgebra S hp).peak i n : A) = G.peak i n := rfl
@[simp] lemma onSubalgebra_trace (a : S) : (G.onSubalgebra S hp).trace a = G.trace a := rfl
@[simp] lemma onSubalgebra_state (i : Bool) (a : S) :
    (G.onSubalgebra S hp).state i a = G.state i a := rfl

lemma onSubalgebra_unique (i : Bool) :
    StateExtensionUnique S.subtype ((G.onSubalgebra S hp).state i) :=
  G.pullback_unique S.subtype Subtype.val_injective (fun i n => ⟨G.peak i n,hp i n⟩) (fun _ _ => rfl) i

variable (T : StarSubalgebra ℂ A) [IsClosed (T : Set A)] (hST : S ≤ T)
  (ht : ∀ i n, G.peak i n ∈ T)

lemma onSubalgebra_natural_peak (i : Bool) (n : ℕ) :
    StarSubalgebra.inclusion hST ((G.onSubalgebra S hp).peak i n) =
      (G.onSubalgebra T ht).peak i n := rfl

lemma onSubalgebra_natural_trace (a : S) :
    (G.onSubalgebra T ht).trace (StarSubalgebra.inclusion hST a) =
      (G.onSubalgebra S hp).trace a := rfl

lemma onSubalgebra_natural_state (i : Bool) :
    restrictState (StarSubalgebra.inclusion hST) ((G.onSubalgebra T ht).state i) =
      (G.onSubalgebra S hp).state i := rfl

include ht in
lemma onSubalgebra_unique_inclusion (i : Bool) :
    StateExtensionUnique (StarSubalgebra.inclusion hST)
      ((G.onSubalgebra S hp).state i) := by
  exact (G.onSubalgebra T ht).pullback_unique (StarSubalgebra.inclusion hST)
    (StarSubalgebra.inclusion_injective hST) ((G.onSubalgebra S hp).peak)
    (fun _ _ => rfl) i

include hST in
lemma onSubalgebra_inequivalent_of_larger
    (hne : ¬ PureStateEquivalent ((G.onSubalgebra T ht).state false)
      ((G.onSubalgebra T ht).peaks false).isPureState
      ((G.onSubalgebra T ht).state true) ((G.onSubalgebra T ht).peaks true).isPureState) :
    ¬ PureStateEquivalent ((G.onSubalgebra S hp).state false)
      ((G.onSubalgebra S hp).peaks false).isPureState
      ((G.onSubalgebra S hp).state true) ((G.onSubalgebra S hp).peaks true).isPureState := by
  intro he
  exact hne (pure_lifts_equivalent (StarSubalgebra.inclusion hST) _ _
    ((G.onSubalgebra S hp).peaks false).isPureState
    ((G.onSubalgebra S hp).peaks true).isPureState he
    (G.onSubalgebra_unique_inclusion S hp T hST ht true) _ _
    ((G.onSubalgebra T ht).peaks false).isPureState
    ((G.onSubalgebra T ht).peaks true).isPureState rfl rfl)

end
section
variable {A B C : Type} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [CStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C]

theorem hnn_ambient_presentation (B₀ : PeakingPairData B) (D : PeakingPairData C)
    (φ : B →⋆ₐ[ℂ] C)
    (hp : ∀ i n, φ (B₀.peak i n) = D.peak i n)
    (ht : ∀ a, D.trace (φ a) = B₀.trace a)
    (Ψ : D.HNNAlgebra →⋆ₐ[ℂ] A) (hΨ : Function.Injective Ψ)
    (ψ : B →⋆ₐ[ℂ] A) (w : Bool → A)
    (hbase : ∀ b, Ψ (D.hnnBase (φ b)) = ψ b)
    (hw : ∀ i, Ψ (D.hnnLetter i) = w i) :
    ∃ e : B₀.HNNAlgebra ≃⋆ₐ[ℂ] hnnGenerated ψ w,
      (∀ b, (e (B₀.hnnBase b) : A) = ψ b) ∧
      (∀ i, (e (B₀.hnnLetter i) : A) = w i) ∧
      (∀ g : A →L[ℂ] ℂ, (∀ b, g (Ψ b) = D.hnnTrace b) →
        ∀ b, g (e b) = B₀.hnnTrace b) := by
  obtain ⟨F,hFi,hFb,hFw,hFt,hFr,_⟩ := B₀.hnn_inclusion_of_peaks D φ hp ht
  have hcomp : Ψ.comp (D.hnnBase.comp φ) = ψ := by ext b; exact hbase b
  have hletter : (fun i => Ψ (D.hnnLetter i)) = w := funext hw
  have hr : (Ψ.comp F).range = hnnGenerated ψ w := by
    rw [StarAlgHom.range_comp_eq_map,hFr,map_hnnGenerated _ _ Ψ hΨ,hcomp,hletter]
  obtain ⟨e,he⟩ := StarAlgHom.equivClosedRange (Ψ.comp F) (hΨ.comp hFi) _ hr
  refine ⟨e,?_,?_,?_⟩
  · intro b
    rw [he]
    change Ψ (F (B₀.hnnBase b)) = _
    rw [hFb,hbase]
  · intro i
    rw [he]
    change Ψ (F (B₀.hnnLetter i)) = _
    rw [hFw,hw]
  · intro g hg b
    rw [he]
    exact (hg (F b)).trans (hFt b)

end

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A C X : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [partialOrderC : PartialOrder C] [starOrderedRingC : StarOrderedRing C]
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]

omit partialOrderC starOrderedRingC in
lemma hnn_hom_ext [PartialOrder C] [StarOrderedRing C] (B : PeakingPairData A) (f g : B.HNNAlgebra →⋆ₐ[ℂ] C)
    (hb : ∀ a, f (B.hnnBase a) = g (B.hnnBase a))
    (hw : ∀ i, f (B.hnnLetter i) = g (B.hnnLetter i)) : f = g := by
  have hfg : (f : B.HNNAlgebra → C) = g := by
    apply Continuous.ext_on B.hnn_generated
      (show Continuous (f : B.HNNAlgebra → C) from (starAlgHomCLM f).continuous)
      (show Continuous (g : B.HNNAlgebra → C) from (starAlgHomCLM g).continuous)
    change StarAlgebra.adjoin ℂ _ ≤ StarAlgHom.equalizer f g
    apply StarAlgHom.adjoin_le_equalizer
    rintro x (⟨a,rfl⟩ | ⟨i,rfl⟩)
    · exact hb a
    · exact hw i
  exact DFunLike.ext _ _ (congrFun hfg)

theorem hnn_reorder_via_equivs (B Q : PeakingPairData A)
    (R : PeakingPairData C) (T : PeakingPairData X)
    (eB : B.HNNAlgebra ≃⋆ₐ[ℂ] C) (eQ : Q.HNNAlgebra ≃⋆ₐ[ℂ] X)
    (ht : ∀ a, B.trace a = Q.trace a)
    (hpR : ∀ i n, eB (B.hnnBase (Q.peak i n)) = R.peak i n)
    (hpT : ∀ i n, eQ (Q.hnnBase (B.peak i n)) = T.peak i n)
    (htR : ∀ x, R.trace (eB x) = B.hnnTrace x)
    (htT : ∀ x, T.trace (eQ x) = Q.hnnTrace x) :
    ∃ e : R.HNNAlgebra ≃⋆ₐ[ℂ] T.HNNAlgebra,
      (∀ a, e (R.hnnBase (eB (B.hnnBase a))) = T.hnnBase (eQ (Q.hnnBase a))) ∧
      (∀ i, e (R.hnnBase (eB (B.hnnLetter i))) = T.hnnLetter i) ∧
      (∀ i, e (R.hnnLetter i) = T.hnnBase (eQ (Q.hnnLetter i))) ∧
      (∀ x, T.hnnTrace (e x) = R.hnnTrace x) := by
  let D := R.pullback eB.toStarAlgHom eB.injective (fun i n => B.hnnBase (Q.peak i n)) hpR
  let E := T.pullback eQ.toStarAlgHom eQ.injective (fun i n => Q.hnnBase (B.peak i n)) hpT
  have htD (x : B.HNNAlgebra) : Q.trace (B.hnnExpectation x) = D.trace x := by
    change Q.trace (B.hnnExpectation x) = R.trace (eB x)
    rw [htR,← ht,B.hnnTrace_expectation]
  have htE (x : Q.HNNAlgebra) : B.trace (Q.hnnExpectation x) = E.trace x := by
    change B.trace (Q.hnnExpectation x) = T.trace (eQ x)
    rw [htT,ht,Q.hnnTrace_expectation]
  obtain ⟨s,hsb,hsB,hsQ,hst⟩ := B.hnn_reorder_of_peaks Q D E ht
    (fun _ _ => rfl) (fun _ _ => rfl) htD htE
  obtain ⟨r,hrb,hrw,hrt,_⟩ := D.hnn_equiv_of_peaks R eB hpR (fun _ => rfl)
  obtain ⟨t,htb,htw,htt,_⟩ := E.hnn_equiv_of_peaks T eQ hpT (fun _ => rfl)
  let e := (r.symm.trans s).trans t
  have her (x : D.HNNAlgebra) : e (r x) = t (s x) := by simp [e]
  refine ⟨e,?_,?_,?_,?_⟩
  · intro a
    rw [← hrb,her,hsb,htb]
  · intro i
    rw [← hrb,her,hsB,htw]
  · intro i
    rw [← hrw,her,hsQ,htb]
  · intro x
    obtain ⟨x,rfl⟩ := r.surjective x
    change T.hnnTrace (e (r x)) = R.hnnTrace (r x)
    rw [her,htt,hst,hrt]

end

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {S R T U A : Type}
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
  [CStarAlgebra U] [PartialOrder U] [StarOrderedRing U] [CStarAlgebra A]

theorem hnn_reorder_ambient_target (B K : PeakingPairData S)
    (D : PeakingPairData R) (E : PeakingPairData T)
    (eP : B.HNNAlgebra ≃⋆ₐ[ℂ] R) (eQ : K.HNNAlgebra ≃⋆ₐ[ℂ] T)
    (eR : D.HNNAlgebra ≃⋆ₐ[ℂ] U)
    (ht : ∀ a, B.trace a = K.trace a)
    (hpD : ∀ i n, eP (B.hnnBase (K.peak i n)) = D.peak i n)
    (hpE : ∀ i n, eQ (K.hnnBase (B.peak i n)) = E.peak i n)
    (htD : ∀ x, D.trace (eP x) = B.hnnTrace x)
    (htE : ∀ x, E.trace (eQ x) = K.hnnTrace x)
    (b : S →⋆ₐ[ℂ] A) (r : R →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (u : U →⋆ₐ[ℂ] A)
    (hu : Function.Injective u) (iTU : T →⋆ₐ[ℂ] U) (hiTU : ∀ a, u (iTU a) = t a)
    (z w : Bool → A)
    (hePb : ∀ a, r (eP (B.hnnBase a)) = b a)
    (hePw : ∀ i, r (eP (B.hnnLetter i)) = z i)
    (heQb : ∀ a, t (eQ (K.hnnBase a)) = b a)
    (heQw : ∀ i, t (eQ (K.hnnLetter i)) = w i)
    (heRb : ∀ a, u (eR (D.hnnBase a)) = r a)
    (heRw : ∀ i, u (eR (D.hnnLetter i)) = w i)
    (g : A →L[ℂ] ℂ) (heRt : ∀ x, g (u (eR x)) = D.hnnTrace x) :
    ∃ e : E.HNNAlgebra ≃⋆ₐ[ℂ] U,
      (∀ a, u (e (E.hnnBase a)) = t a) ∧
      (∀ i, u (e (E.hnnLetter i)) = z i) ∧
      (∀ x, g (u (e x)) = E.hnnTrace x) := by
  obtain ⟨s,hsb,hsP,hsQ,hst⟩ := B.hnn_reorder_via_equivs K D E eP eQ ht hpD hpE htD htE
  let e : E.HNNAlgebra ≃⋆ₐ[ℂ] U := s.symm.trans eR
  have hes (x : D.HNNAlgebra) : e (s x) = eR x := by simp [e]
  have hsP' (i : Bool) : e (E.hnnLetter i) = eR (D.hnnBase (eP (B.hnnLetter i))) := by
    rw [← hsP,hes]
  have hsQ' (i : Bool) : e (E.hnnBase (eQ (K.hnnLetter i))) = eR (D.hnnLetter i) := by
    rw [← hsQ,hes]
  have hsb' (a : S) : e (E.hnnBase (eQ (K.hnnBase a))) =
      eR (D.hnnBase (eP (B.hnnBase a))) := by rw [← hsb,hes]
  let f : K.HNNAlgebra →⋆ₐ[ℂ] U := (e.toStarAlgHom.comp E.hnnBase).comp eQ.toStarAlgHom
  let h : K.HNNAlgebra →⋆ₐ[ℂ] U := iTU.comp eQ.toStarAlgHom
  have hfg : f = h := by
    apply K.hnn_hom_ext f h
    · intro a
      apply hu
      change u (e (E.hnnBase (eQ (K.hnnBase a)))) = u (iTU (eQ (K.hnnBase a)))
      rw [hsb',heRb,hePb,hiTU,heQb]
    · intro i
      apply hu
      change u (e (E.hnnBase (eQ (K.hnnLetter i)))) = u (iTU (eQ (K.hnnLetter i)))
      rw [hsQ',heRw,hiTU,heQw]
  refine ⟨e,?_,?_,?_⟩
  · intro a
    obtain ⟨c,hc⟩ := eQ.surjective a
    change eQ c = a at hc
    have hh := congrArg (fun F : K.HNNAlgebra →⋆ₐ[ℂ] U => u (F c)) hfg
    change u (e (E.hnnBase (eQ c))) = u (iTU (eQ c)) at hh
    rw [hiTU,hc] at hh
    exact hh
  · intro i
    rw [hsP',heRb,hePw]
  · intro x
    obtain ⟨c,hc⟩ := s.surjective x
    change s c = x at hc
    have hh : g (u (e (s c))) = E.hnnTrace (s c) := by rw [hes,heRt,hst]
    simpa only [hc] using hh

end

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {S R T U A : Type}
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
  [CStarAlgebra U] [PartialOrder U] [StarOrderedRing U] [CStarAlgebra A]

theorem hnn_reorder_from_ambient_data (B K : PeakingPairData S)
    (D : PeakingPairData R) (E : PeakingPairData T)
    (eP : B.HNNAlgebra ≃⋆ₐ[ℂ] R) (eQ : K.HNNAlgebra ≃⋆ₐ[ℂ] T)
    (eR : D.HNNAlgebra ≃⋆ₐ[ℂ] U)
    (b : S →⋆ₐ[ℂ] A) (r : R →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (u : U →⋆ₐ[ℂ] A)
    (hr : Function.Injective r) (ht : Function.Injective t) (hu : Function.Injective u)
    (iTU : T →⋆ₐ[ℂ] U) (hiTU : ∀ a, u (iTU a) = t a)
    (hpD : ∀ i n, b (K.peak i n) = r (D.peak i n))
    (hpE : ∀ i n, b (B.peak i n) = t (E.peak i n))
    (g : A →L[ℂ] ℂ)
    (hBt : ∀ a, B.trace a = g (b a)) (hKt : ∀ a, K.trace a = g (b a))
    (hDt : ∀ a, D.trace a = g (r a)) (hEt : ∀ a, E.trace a = g (t a))
    (z w : Bool → A)
    (hePb : ∀ a, r (eP (B.hnnBase a)) = b a)
    (hePw : ∀ i, r (eP (B.hnnLetter i)) = z i)
    (heQb : ∀ a, t (eQ (K.hnnBase a)) = b a)
    (heQw : ∀ i, t (eQ (K.hnnLetter i)) = w i)
    (heRb : ∀ a, u (eR (D.hnnBase a)) = r a)
    (heRw : ∀ i, u (eR (D.hnnLetter i)) = w i)
    (hePt : ∀ x, g (r (eP x)) = B.hnnTrace x)
    (heQt : ∀ x, g (t (eQ x)) = K.hnnTrace x)
    (heRt : ∀ x, g (u (eR x)) = D.hnnTrace x) :
    ∃ e : E.HNNAlgebra ≃⋆ₐ[ℂ] U,
      (∀ a, u (e (E.hnnBase a)) = t a) ∧
      (∀ i, u (e (E.hnnLetter i)) = z i) ∧
      (∀ x, g (u (e x)) = E.hnnTrace x) := by
  have hBK (a : S) : B.trace a = K.trace a := (hBt a).trans (hKt a).symm
  have hD (i : Bool) (n : ℕ) : eP (B.hnnBase (K.peak i n)) = D.peak i n :=
    hr ((hePb _).trans (hpD i n))
  have hE (i : Bool) (n : ℕ) : eQ (K.hnnBase (B.peak i n)) = E.peak i n :=
    ht ((heQb _).trans (hpE i n))
  exact B.hnn_reorder_ambient_target K D E eP eQ eR hBK hD hE
    (fun x => (hDt _).trans (hePt x)) (fun x => (hEt _).trans (heQt x))
    b r t u hu iTU hiTU z w hePb hePw heQb heQw heRb heRw g heRt

end

end PeakingPairData

open Topology
namespace PeakingPairData

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A C X : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [CStarAlgebra X]

lemma hnnGenerated_eq_top (B : PeakingPairData A) :
    hnnGenerated B.hnnBase B.hnnLetter = ⊤ := by
  apply top_unique
  intro x _
  exact B.hnn_generated x

lemma hnn_image_generated (B : PeakingPairData A) (φ : B.HNNAlgebra →⋆ₐ[ℂ] C)
    (hφ : Function.Injective φ) :
    φ.range = hnnGenerated (φ.comp B.hnnBase) (fun i => φ (B.hnnLetter i)) := by
  have H := map_hnnGenerated B.hnnBase B.hnnLetter φ hφ
  have htop : (⊤ : StarSubalgebra ℂ B.HNNAlgebra).map φ = φ.range := by
    ext c
    constructor
    · rintro ⟨b,_,rfl⟩; exact ⟨b,rfl⟩
    · rintro ⟨b,rfl⟩; exact ⟨b,trivial,rfl⟩
  rw [B.hnnGenerated_eq_top,htop] at H
  exact H

lemma hnn_equiv_image_generated (B : PeakingPairData A)
    (e : B.HNNAlgebra ≃⋆ₐ[ℂ] X) (ψ : X →⋆ₐ[ℂ] C) (hψ : Function.Injective ψ) :
    ψ.range = hnnGenerated ((ψ.comp e.toStarAlgHom).comp B.hnnBase)
      (fun i => ψ (e (B.hnnLetter i))) := by
  have H := B.hnn_image_generated (ψ.comp e.toStarAlgHom) (hψ.comp e.injective)
  have hr : (ψ.comp e.toStarAlgHom).range = ψ.range := by
    ext c
    constructor
    · rintro ⟨b,rfl⟩; exact ⟨e b,rfl⟩
    · rintro ⟨x,rfl⟩
      obtain ⟨b,rfl⟩ := e.surjective x
      exact ⟨b,rfl⟩
  rw [hr] at H
  exact H
end

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {S R T U A : Type}
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [CStarAlgebra T] [partialOrderT : PartialOrder T] [starOrderedRingT : StarOrderedRing T]
  [CStarAlgebra U] [PartialOrder U] [StarOrderedRing U]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def HNNAmbientPresentation (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A) : Prop :=
  ∃ B : PeakingPairData S,
    (∀ i n, b (B.peak i n) = G.peak i n) ∧
    (∀ a : S, B.trace a = G.trace (b a)) ∧
    ∃ e : B.HNNAlgebra ≃⋆ₐ[ℂ] T,
      (∀ a, t (e (B.hnnBase a)) = b a) ∧
      (∀ i, t (e (B.hnnLetter i)) = z i) ∧
      (∀ a, G.trace (t (e a)) = B.hnnTrace a)

omit partialOrderT starOrderedRingT in
lemma HNNAmbientPresentation.generated [PartialOrder T] [StarOrderedRing T] (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (ht : Function.Injective t) (h : G.HNNAmbientPresentation b t z) :
    t.range = hnnGenerated b z := by
  obtain ⟨B,_,_,e,heb,hew,_⟩ := h
  have H := B.hnn_equiv_image_generated e t ht
  have hb : (t.comp e.toStarAlgHom).comp B.hnnBase = b := by ext a; exact heb a
  have hw : (fun i => t (e (B.hnnLetter i))) = z := funext hew
  rw [hb,hw] at H
  exact H

lemma HNNAmbientPresentation.swap (P Q : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (r : R →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (u : U →⋆ₐ[ℂ] A)
    (hr : Function.Injective r) (ht : Function.Injective t) (hu : Function.Injective u)
    (iTU : T →⋆ₐ[ℂ] U) (hiTU : ∀ a, u (iTU a) = t a)
    (z w : Bool → A) (htrace : ∀ a, P.trace a = Q.trace a)
    (hP : P.HNNAmbientPresentation b r z)
    (hQ : Q.HNNAmbientPresentation b t w)
    (hR : Q.HNNAmbientPresentation r u w)
    (E : PeakingPairData T) (ep : ∀ i n, t (E.peak i n) = P.peak i n)
    (et : ∀ a, E.trace a = P.trace (t a)) : P.HNNAmbientPresentation t u z := by
  obtain ⟨B,pb,pt,eP,hePb,hePw,hePt⟩ := hP
  obtain ⟨K,qb,qt,eQ,heQb,heQw,heQt⟩ := hQ
  obtain ⟨D,qd,qdt,eR,heRb,heRw,heRt⟩ := hR
  refine ⟨E,ep,et,?_⟩
  exact B.hnn_reorder_from_ambient_data K D E eP eQ eR
    b r t u hr ht hu iTU hiTU
    (fun i n => (qb i n).trans (qd i n).symm)
    (fun i n => (pb i n).trans (ep i n).symm)
    (positiveCLM P.trace) pt
    (fun a => (qt a).trans (htrace _).symm)
    (fun a => (qdt a).trans (htrace _).symm) et
    z w hePb hePw heQb heQw heRb heRw
    hePt (fun x => (htrace _).trans (heQt x)) (fun x => (htrace _).trans (heRt x))

end

end PeakingPairData

end NaimarkZFC

end

end OAI
