import OAI.MathematicalPhysics.Elasticity.WeakLimits

namespace OAI

noncomputable section

/- The exact extension proofs are reused from their canonical original module. -/

namespace ElasticityGraph
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
/-- Orthogonal projection supplies a genuine bounded left inverse of a
coercive Hilbert operator on all of the target space. -/
theorem exists_coercive_left_inverse (A : E →L[ℂ] F) (C : ℝ) (hC : 0≤C)
    (hA : ∀ x, ‖x‖≤C*‖A x‖) :
    ∃ R : F →L[ℂ] E, R.comp A=ContinuousLinearMap.id ℂ E := by
  have hal : AntilipschitzWith ⟨C,hC⟩ A := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    change dist x y≤C*dist (A x) (A y)
    simpa only [dist_eq_norm,← map_sub] using hA (x-y)
  have hclosed : IsClosed (Set.range A) := hal.isClosed_range A.uniformContinuous
  let e : E ≃L[ℂ] A.range := A.equivRange hal.injective hclosed
  let : CompleteSpace A.range := hclosed.completeSpace_coe
  let R : F →L[ℂ] E := e.symm.toContinuousLinearMap.comp A.range.orthogonalProjectionOnto
  refine ⟨R,?_⟩
  ext x
  change e.symm (A.range.orthogonalProjectionOnto (A x))=x
  have hx : A.range.orthogonalProjectionOnto (A x)=e x :=
    A.range.orthogonalProjectionOnto_mem_subspace_eq_self (e x)
  rw [hx,ContinuousLinearEquiv.symm_apply_apply]
end ElasticityGraph
namespace ElasticityGraph
open Set
open ElasticityRegularity
variable {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

  [NormedAddCommGroup P] [NormedSpace ℝ P]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
local instance : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
/-- A smooth local left inverse, with no surjectivity hypothesis. -/
theorem local_smooth_left_inverse (A : P → E →L[ℂ] F)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (p₀ : P) (C : ℝ) (hC : 0≤C)
    (hbound : ∀ x, ‖x‖≤C*‖A p₀ x‖) :
    ∃ (U : Set P) (R : P → F →L[ℂ] E), IsOpen U ∧ p₀∈U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) R U ∧ ∀ p∈U, (R p).comp (A p)=ContinuousLinearMap.id ℂ E := by
  obtain ⟨R₀,hR₀⟩ := exists_coercive_left_inverse (A p₀) C hC hbound
  let B : P → E →L[ℂ] E := fun p => R₀.comp (A p-A p₀)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := complex_clm_comp_smooth contDiff_const (hA.sub contDiff_const)
  let U : Set P := {p | ‖B p‖<1}
  have hopen : IsOpen U := isOpen_lt hB.continuous.norm continuous_const
  have hmem : p₀∈U := by simp only [U,B,mem_ofPred_eq,sub_self,ContinuousLinearMap.comp_zero,norm_zero,zero_lt_one]
  let R : P → F →L[ℂ] E := fun p => (Ring.inverse (1+B p)).comp R₀
  have hu (p : P) (hp : p∈U) : IsUnit (1+B p) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one
      (by simpa only [norm_neg] using (show ‖B p‖<1 from hp) : ‖-(B p)‖<1)
  have hi (p : P) (hp : p∈U) : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => Ring.inverse (1+B q)) p := by
    obtain ⟨v,hv⟩ := hu p hp
    have hInv : ContDiffAt ℝ (⊤ : ℕ∞) Ring.inverse (1+B p) := by
      rw [← hv]
      exact contDiffAt_ringInverse ℝ v
    exact hInv.comp p (contDiffAt_const.add hB.contDiffAt)
  have hR : ContDiffOn ℝ (⊤ : ℕ∞) R U := by
    intro p hp
    let L : (E →L[ℂ] E) →L[ℂ] (F →L[ℂ] E) := (ContinuousLinearMap.compL ℂ F E E).flip R₀
    exact ((L.restrictScalars ℝ).contDiff.contDiffAt.comp p (hi p hp)).contDiffWithinAt
  refine ⟨U,R,hopen,hmem,hR,fun p hp => ?_⟩
  have hRA : R₀.comp (A p)=1+B p := by
    dsimp [B]
    rw [ContinuousLinearMap.comp_sub,hR₀]
    change R₀.comp (A p)=ContinuousLinearMap.id ℂ E+(R₀.comp (A p)-ContinuousLinearMap.id ℂ E)
    abel
  change (Ring.inverse (1+B p)).comp (R₀.comp (A p))=1
  rw [hRA]
  exact Ring.inverse_mul_cancel _ (hu p hp)

/-- Smooth dependence and existence at all parameters follow from existence
on a dense set, using the actual local Hilbert left inverse. -/
theorem local_smooth_solution_of_dense (A : P → E →L[ℂ] F)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (f : P → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {D : Set P} (hD : Dense D) (hex : ∀ p∈D, ∃ u, A p u=f p)
    (p₀ : P) (C : ℝ) (hC : 0≤C) (hbound : ∀ x, ‖x‖≤C*‖A p₀ x‖) :
    ∃ (U : Set P) (u : P → E), IsOpen U ∧ p₀∈U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u U ∧ ∀ p∈U, A p (u p)=f p := by
  obtain ⟨U,R,hU,hp,hR,he⟩ := local_smooth_left_inverse A hA p₀ C hC hbound
  let u : P → E := fun p => R p (f p)
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) u U :=
    (((ContinuousLinearMap.restrictScalarsL ℂ F E ℝ ℝ).contDiff.comp_contDiffOn hR).clm_apply hf.contDiffOn)
  have hr : ContinuousOn (fun p => A p (u p)) U :=
    (((ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).contDiff.comp hA).contDiffOn.clm_apply hu).continuousOn
  have hdense : EqOn (fun p => A p (u p)) f (U∩D) := by
    intro p hp
    obtain ⟨v,hv⟩ := hex p hp.2
    have hl := congrArg (fun L : E →L[ℂ] E => L v) (he p hp.1)
    change R p (A p v)=v at hl
    dsimp [u]
    rw [← hv,hl]
  exact ⟨U,u,hU,hp,hu,hdense.of_subset_closure hr hf.continuous.continuousOn
    inter_subset_left (hD.open_subset_closure_inter hU)⟩
end ElasticityGraph
namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

section
variable {n : Type*} [Fintype n]
abbrev GraphSpace (n : Type*) := WithLp 2 (Hilbert n × Hilbert n)
def testGraph (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) : supported (n := n) S →ₗ[ℂ] GraphSpace n :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (Hilbert n) (Hilbert n)).symm.toLinearMap.comp
    ((embed.comp (supported S).subtype).prod
      ((embed.comp (transport a ha)).comp (supported S).subtype))
def closedGraph (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) : Submodule ℂ (GraphSpace n) :=
  (testGraph S a ha).range.topologicalClosure
instance graphComplete (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) : CompleteSpace (closedGraph S a ha) :=
  (testGraph S a ha).range.isClosed_topologicalClosure.completeSpace_coe

def graphFirst (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) : closedGraph S a ha →L[ℂ] Hilbert n :=
  (WithLp.fstL 2 ℂ (Hilbert n) (Hilbert n)).comp (closedGraph S a ha).subtypeL
def graphSecond (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) : closedGraph S a ha →L[ℂ] Hilbert n :=
  (WithLp.sndL 2 ℂ (Hilbert n) (Hilbert n)).comp (closedGraph S a ha).subtypeL

/-- The positive-commutator coercivity survives the actual graph closure. -/
theorem closed_graph_estimate {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∀ u : closedGraph S a ha,
      ‖u‖≤C*‖graphSecond S a ha u‖ := by
  obtain ⟨C,hC,hest⟩ := supported_transport_estimate hS a ha
  have hcl : ∀ u : closedGraph S a ha, ‖graphFirst S a ha u‖≤C*‖graphSecond S a ha u‖ := by
    intro u
    have hclosed : IsClosed {v : GraphSpace n | ‖v.fst‖≤C*‖v.snd‖} :=
      isClosed_le (WithLp.fstL 2 ℂ (Hilbert n) (Hilbert n)).continuous.norm
        (continuous_const.mul (WithLp.sndL 2 ℂ (Hilbert n) (Hilbert n)).continuous.norm)
    have hincl : (testGraph S a ha).range ≤
        {v : GraphSpace n | ‖v.fst‖≤C*‖v.snd‖} := by
      rintro v ⟨w,rfl⟩
      exact hest w w.property
    exact closure_minimal hincl hclosed u.property
  refine ⟨C+1,by linarith,fun u => ?_⟩
  have h := hcl u
  have hn := WithLp.prod_norm_sq_eq_of_L2 (u : GraphSpace n)
  change ‖u‖^2=‖graphFirst S a ha u‖^2+‖graphSecond S a ha u‖^2 at hn
  have hp : 0≤C*‖graphSecond S a ha u‖ := mul_nonneg hC.le (norm_nonneg _)
  have hsq := sq_le_sq₀ (norm_nonneg (graphFirst S a ha u)) hp |>.mpr h
  have hx := norm_nonneg u
  have hy := norm_nonneg (graphSecond S a ha u)
  nlinarith [sq_nonneg (C*‖graphSecond S a ha u‖),mul_nonneg hC.le (sq_nonneg ‖graphSecond S a ha u‖)]
end
open ElasticityRegularity
variable {n : Type*} [Fintype n]
lemma L2_distribution (u : Test) : (L2 u : 𝓢'(ℂ,ℂ))=(toSchwartz u : 𝓢'(ℂ,ℂ)) :=
  Lp.toTemperedDistribution_toLp_eq (toSchwartz u)
lemma planarOperator_test (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u : n → Test) (i : n) :
    planarOperator a i (embed u)=entryInjection i (embed (transport a (fun i j => (ha i j).1) u)) := by
  simp only [planarOperator_apply,entryInjection_apply,embed_apply,L2_distribution,dbar_schwartz]
  have ht : toSchwartz (transport a (fun i j => (ha i j).1) u i)=
      schwartzDbar (toSchwartz (u i))+∑ j, SchwartzMap.smulLeftCLM ℂ (a i j) (toSchwartz (u j)) := by
    simp only [transport,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_smul,map_sum,
      toSchwartz_d,schwartzDbar]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => toSchwartz_mul (a i j) (ha i j) (u j))
  rw [ht,map_add,map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => distribution_schwartz_product (ha i j) (toSchwartz (u j)))

/-- Closing compact test graphs preserves the actual distributional operator. -/
theorem graph_equation (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u : closedGraph S a (fun i j => (ha i j).1)) (i : n) :
    planarOperator a i (graphFirst S a (fun i j => (ha i j).1) u)=
      entryInjection i (graphSecond S a (fun i j => (ha i j).1) u) := by
  let F := (planarOperator a i).comp (WithLp.fstL 2 ℂ (Hilbert n) (Hilbert n))
  let G := (entryInjection i).comp (WithLp.sndL 2 ℂ (Hilbert n) (Hilbert n))
  have hc : IsClosed {v : GraphSpace n | F v=G v} := isClosed_eq F.continuous G.continuous
  have hsub : ((testGraph S a (fun i j => (ha i j).1)).range : Set (GraphSpace n)) ⊆ {v | F v=G v} := by
    rintro v ⟨w,rfl⟩
    exact planarOperator_test a ha w i
  exact closure_minimal hsub hc u.property

lemma test_support_distribution {S : Set ℂ} (u : Test) (hu : tsupport (u : ℂ → ℂ)⊆S) :
    LocalEqual Sᶜ (L2 u : 𝓢'(ℂ,ℂ)) 0 := by
  intro φ _ hs
  rw [L2_distribution]
  change (∫ z : ℂ, φ z • toSchwartz u z)=0
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  by_cases hz : z∈S
  · have hz' : z∉tsupport (φ : ℂ → ℂ) := fun h => hs h hz
    rw [image_eq_zero_of_notMem_tsupport hz',zero_smul]
    rfl
  · have hz' : z∉tsupport (u : ℂ → ℂ) := fun h => hz (hu h)
    rw [toSchwartz_apply,image_eq_zero_of_notMem_tsupport hz',smul_zero]
    rfl

/-- Graph closure retains support, in the literal distributional sense. -/
theorem graph_support (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (u : closedGraph S a ha) (i : n) :
    LocalEqual Sᶜ (entryInjection i (graphFirst S a ha u)) 0 := by
  intro φ hc hs
  let F : GraphSpace n →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp ((entryInjection i).comp (WithLp.fstL 2 ℂ (Hilbert n) (Hilbert n)))
  have hclosed : IsClosed {v : GraphSpace n | F v=0} := isClosed_eq F.continuous continuous_const
  have hsub : ((testGraph S a ha).range : Set (GraphSpace n)) ⊆ {v | F v=0} := by
    rintro v ⟨w,rfl⟩
    exact test_support_distribution (w.val i) (w.property i) φ hc hs
  exact closure_minimal hsub hclosed u.property
end ElasticityPlanar
namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
lemma shifted_graph_equation {S : Set ℂ} (a b : n → n → ℂ → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (M : Hilbert n →L[ℂ] Hilbert n)
    (hM : ∀ w i, entryInjection i (M w)=
      ∑ j, smulLeftCLM ℂ (b i j) (entryInjection j w)-
        ∑ j, smulLeftCLM ℂ (a i j) (entryInjection j w))
    (u : closedGraph S a (fun i j => (ha i j).1)) (i : n) :
    planarOperator b i (graphFirst S a (fun i j => (ha i j).1) u)=
      entryInjection i ((graphSecond S a (fun i j => (ha i j).1)+
        M.comp (graphFirst S a (fun i j => (ha i j).1))) u) := by
  have h₀ := graph_equation S a ha u i
  simp only [add_apply,ContinuousLinearMap.comp_apply,map_add,hM]
  rw [← h₀,planarOperator_apply,planarOperator_apply]
  simp only [entryInjection_apply]
  abel

lemma graph_test_solution {S : Set ℂ} (a b : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (A : closedGraph S a ha →L[ℂ] Hilbert n)
    (hA : ∀ u i, planarOperator b i (graphFirst S a ha u)=entryInjection i (A u))
    (f : Hilbert n) (v : n → Test) (hv : ∀ i, tsupport (v i : ℂ → ℂ)⊆S)
    (heq : ∀ i, planarOperator b i (embed v)=entryInjection i f) :
    ∃ u : closedGraph S a ha, A u=f := by
  let w : closedGraph S a ha := ⟨testGraph S a ha ⟨v,hv⟩,
    (testGraph S a ha).range.le_topologicalClosure ⟨⟨v,hv⟩,rfl⟩⟩
  refine ⟨w,?_⟩
  apply PiLp.ext
  intro i
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  change entryInjection i (A w)=entryInjection i f
  rw [← hA w i]
  exact heq i

omit [FiniteDimensional ℝ P] in
lemma local_graph_solution {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (A : P → closedGraph S a ha →L[ℂ] Hilbert n)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (p₀ : P) (hA₀ : A p₀=graphSecond S a ha)
    (f : P → Hilbert n) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {D : Set P} (hD : Dense D) (hex : ∀ p∈D, ∃ u : closedGraph S a ha, A p u=f p) :
    ∃ (U : Set P) (u : P → closedGraph S a ha), IsOpen U ∧ p₀∈U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u U ∧ ∀ p∈U, A p (u p)=f p := by
  obtain ⟨C,hC,hbound⟩ := closed_graph_estimate hS a ha
  exact ElasticityGraph.local_smooth_solution_of_dense (E := closedGraph S a ha) (F := Hilbert n) A hA f hf hD hex p₀ C hC.le
    (fun x => by rw [hA₀]; exact hbound x)

/-- A local smooth supported solution family, derived from compact-test graph
solvability on a dense set. No range-surjectivity assumption is required. -/
theorem local_supported_of_dense_tests {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
    (f : P → Hilbert n) (hf : ContDiff ℝ (⊤ : ℕ∞) f) {D : Set P} (hD : Dense D)
    (hex : ∀ p∈D, ∃ v : n → Test, (∀ i, tsupport (v i : ℂ → ℂ)⊆S) ∧
      ∀ i, planarOperator (fun i j z => a i j (p,z)) i (embed v)=entryInjection i (f p))
    (p₀ : P) :
    ∃ (U : Set P) (u : P → Hilbert n), IsOpen U ∧ p₀∈U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u U ∧ ∀ p∈U, ∀ i,
        planarOperator (fun i j z => a i j (p,z)) i (u p)=entryInjection i (f p) ∧
        LocalEqual Sᶜ (entryInjection i (u p)) 0 := by
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) p).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  let a₀ : n → n → ℂ → ℂ := fun i j z => a i j (p₀,z)
  let ha₀ := fun i j => (hat p₀ i j).1
  obtain ⟨M,hM,hMe⟩ := exists_smooth_matrix_multiplier hK a ha hs
  let I : closedGraph S a₀ ha₀ →L[ℂ] Hilbert n := graphFirst S a₀ ha₀
  let J : closedGraph S a₀ ha₀ →L[ℂ] Hilbert n := graphSecond S a₀ ha₀
  let A : P → closedGraph S a₀ ha₀ →L[ℂ] Hilbert n := fun p => J+(M p-M p₀).comp I
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := contDiff_const.add
    (complex_clm_comp_smooth (hM.sub contDiff_const) contDiff_const)
  have he (p : P) (u : closedGraph S a₀ ha₀) (i : n) :
      planarOperator (fun i j z => a i j (p,z)) i (I u)=entryInjection i (A p u) := by
    apply shifted_graph_equation a₀ (fun i j z => a i j (p,z)) (hat p₀)
      (M p-M p₀) (fun w k => ?_) u i
    simp only [sub_apply,map_sub,entryInjection_apply,hMe p,hMe p₀]
    rfl
  have hex' : ∀ p∈D, ∃ u : closedGraph S a₀ ha₀, A p u=f p := by
    intro p hp
    obtain ⟨v,hv,heq⟩ := hex p hp
    exact graph_test_solution a₀ (fun i j z => a i j (p,z)) ha₀ (A p) (he p) (f p) v hv heq
  have hA₀ : A p₀=graphSecond S a₀ ha₀ := by
    simp only [A,sub_self,ContinuousLinearMap.zero_comp,add_zero,J]
  obtain ⟨U,u,hU,hp₀,hu,huEq⟩ := local_graph_solution hS a₀ ha₀ A hA p₀ hA₀ f hf hD hex'
  refine ⟨U,fun p => I (u p),hU,hp₀,(I.restrictScalars ℝ).contDiff.comp_contDiffOn hu,fun p hp i => ?_⟩
  exact ⟨(he p (u p) i).trans (congrArg (entryInjection i) (huEq p hp)),graph_support S a₀ ha₀ (u p) i⟩
end ElasticityPlanar
namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution

section
open scoped ENNReal SchwartzMap
open ElasticityRegularity
lemma supported_smooth_test {S : Set ℂ} (hS : IsCompact S)
    (u : Lp ℂ 2 (volume : Measure ℂ))
    (hu : ∀ N : ℕ, LocalSobolev univ N (u : 𝓢'(ℂ,ℂ)))
    (hs : LocalEqual Sᶜ (u : 𝓢'(ℂ,ℂ)) 0) :
    ∃ v : Test, L2 v=u ∧ tsupport (v : ℂ → ℂ)⊆S := by
  obtain ⟨R,hR,hSR⟩ := hS.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : ℂ) := ⟨R,R+1,hR,by simp⟩
  let c : ContDiffBump (0 : ℂ) := ⟨R+3,R+4,by linarith,by linarith⟩
  have hc : HasCompactSupport (fun z : ℂ => (c z : ℂ)) :=
    c.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  have hcs : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (c z : ℂ)) := Complex.ofRealCLM.contDiff.comp c.contDiff
  have h1 : EqOn (fun z : ℂ => (c z : ℂ)) 1 (Metric.ball 0 (R+3)) := by
    intro z hz
    change (c z : ℂ)=1
    rw [c.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)]
    rfl
  obtain ⟨w,_,hw⟩ := local_schwartz_l2_representative Metric.isOpen_ball u hu hcs hc (subset_univ _) h1
  have hb : HasCompactSupport (fun z : ℂ => (b z : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  let v : Test := ⟨fun z => (b z : ℂ)*w z,
    ⟨(Complex.ofRealCLM.contDiff.comp b.contDiff).mul (w.smooth ⊤),hb.mul_right⟩⟩
  have hs' : LocalEqual Sᶜ (u : 𝓢'(ℂ,ℂ)) ((0 : Lp ℂ 2 (volume : Measure ℂ)) : 𝓢'(ℂ,ℂ)) := by
    change LocalEqual Sᶜ (u : 𝓢'(ℂ,ℂ)) ((Lp.toTemperedDistributionCLM ℂ volume 2) 0)
    rw [map_zero]
    exact hs
  have hzero := LocalEqual.lp_ae hS.isClosed.isOpen_compl u 0 hs'
  have hev : L2 v=u := by
    apply Lp.ext
    filter_upwards [(toSchwartz v).coeFn_toLp 2 volume,hw,hzero,Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz hzB hzout hz0
    change (L2 v : ℂ → ℂ) z=v z at hz
    rw [hz]
    change (b z : ℂ)*w z=u z
    by_cases hzS : z∈S
    · have hzn : ‖z‖≤R := hSR z hzS
      have hzB' : z∈Metric.ball 0 (R+3) := by simpa only [Metric.mem_ball,dist_zero_right] using (show ‖z‖<R+3 by linarith)
      have hzb : z∈Metric.closedBall 0 b.rIn := by simpa only [b,Metric.mem_closedBall,dist_zero_right] using hzn
      rw [b.one_of_mem_closedBall hzb,Complex.ofReal_one,one_mul]
      exact (hzB hzB').symm
    · have hu0 : u z=0 := (hzout hzS).trans hz0
      rw [hu0]
      by_cases hzB' : z∈Metric.ball 0 (R+3)
      · rw [← hzB hzB',hu0,mul_zero]
      · have hn : R+3≤‖z‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hzB'
        rw [b.zero_of_le_dist (by change R+1≤dist z 0; rw [dist_zero_right]; linarith),Complex.ofReal_zero,zero_mul]
  refine ⟨v,hev,?_⟩
  have hveq : LocalEqual Sᶜ (toSchwartz v : 𝓢'(ℂ,ℂ)) ((0 : 𝓢(ℂ,ℂ)) : 𝓢'(ℂ,ℂ)) := by
    rw [← L2_distribution,hev,map_zero]
    exact hs
  have hpt := hveq.schwartz_eqOn hS.isClosed.isOpen_compl
  apply closure_minimal _ hS.isClosed
  intro z hz
  by_contra hzS
  exact hz (hpt hzS)
end
open scoped ENNReal SchwartzMap BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
lemma operator_all_orders (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (w : Hilbert n) (f : n → 𝓢(ℂ,ℂ))
    (he : ∀ i, planarOperator a i w=(f i : 𝓢'(ℂ,ℂ))) :
    ∀ N : ℕ, ∀ i, LocalSobolev univ N (entryInjection i w) := by
  have he' : ElasticityPlanarDistribution.Equation univ (fun i j z => -a i j z)
      (fun j => (w j : 𝓢'(ℂ,ℂ))) (fun j => (f j : 𝓢'(ℂ,ℂ))) := by
    intro i φ _ _
    have hh := congrArg (fun v : 𝓢'(ℂ,ℂ) => v φ) (he i)
    rw [planarOperator_apply] at hh
    have hn (j : n) : smulLeftCLM ℂ (fun z => -a i j z) (w j : 𝓢'(ℂ,ℂ))=
        -smulLeftCLM ℂ (a i j) (w j : 𝓢'(ℂ,ℂ)) := by
      change smulLeftCLM ℂ (-(a i j)) (w j : 𝓢'(ℂ,ℂ))=_
      rw [smulLeftCLM_neg (ha i j),neg_apply]
    simp only [hn,Finset.sum_neg_distrib,add_apply,neg_apply] at hh ⊢
    linear_combination hh
  exact ElasticityPlanarDistribution.local_all_orders (fun i j z => -a i j z)
    (fun i j => (ha i j).neg) (fun j => (w j : 𝓢'(ℂ,ℂ))) (fun j => (f j : 𝓢'(ℂ,ℂ))) he'
    (fun j => MemSobolev.local_zero (memSobolev_zero_iff.mpr ⟨w j,rfl⟩) univ)
    (fun N j g hg hc _ => sobolev_nat_product Complex.orthonormalBasisOneI N hg hc (f j).memSobolev)

/-- Smooth forcing upgrades every supported weak L2 solution to an actual compact
smooth test vector, by the established elliptic regularity and support identity. -/
theorem supported_weak_is_test {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (w : Hilbert n) (f : n → 𝓢(ℂ,ℂ))
    (he : ∀ i, planarOperator a i w=(f i : 𝓢'(ℂ,ℂ)))
    (hs : ∀ i, LocalEqual Sᶜ (entryInjection i w) 0) :
    ∃ v : n → Test, embed v=w ∧ ∀ i, tsupport (v i : ℂ → ℂ)⊆S := by
  have hall := operator_all_orders a ha w f he
  choose v hv hvs using fun i => supported_smooth_test hS (w i) (fun N => hall N i) (hs i)
  refine ⟨v,?_,hvs⟩
  apply PiLp.ext
  exact hv

/-- Compact support gives uniqueness for the genuine weak transport operator. -/
theorem supported_weak_kernel {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (w : Hilbert n) (he : ∀ i, planarOperator a i w=0)
    (hs : ∀ i, LocalEqual Sᶜ (entryInjection i w) 0) : w=0 := by
  obtain ⟨v,hv,hvs⟩ := supported_weak_is_test hS a ha w (fun _ => 0)
    (fun i => by simpa only [map_zero] using he i) hs
  have htr : embed (transport a (fun i j => (ha i j).1) v)=0 := by
    apply PiLp.ext
    intro i
    apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
    change entryInjection i (embed (transport a (fun i j => (ha i j).1) v))=entryInjection i 0
    rw [← planarOperator_test a ha v i,hv,he i,map_zero]
  obtain ⟨C,_,hC⟩ := supported_transport_estimate hS a (fun i j => (ha i j).1)
  have h := hC v hvs
  rw [htr,norm_zero,mul_zero,hv] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg w))
end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal BigOperators Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
lemma compact_smooth_source {K : Set ℂ} (hK : IsCompact K)
    (f : n → P × ℂ → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hs : ∀ i p z, z∉K → f i (p,z)=0) :
    ∃ (F : P → n → 𝓢(ℂ,ℂ)) (w : P → Hilbert n),
      (∀ p i z, F p i z=f i (p,z)) ∧
      (∀ N : ℕ, ∀ i, SmoothSobolev N (fun p => (F p i : 𝓢'(ℂ,ℂ)))) ∧
      ContDiff ℝ (⊤ : ℕ∞) w ∧ ∀ p i, entryInjection i (w p)=(F p i : 𝓢'(ℂ,ℂ)) := by
  choose F hFe hF using fun i => compact_smooth_sobolev hK (f i) (hf i) (hs i)
  have hF₀ (i : n) : ∃ w : P → PL2, ContDiff ℝ (⊤ : ℕ∞) w ∧
      ∀ p, (w p : 𝓢'(ℂ,ℂ))=(F i p : 𝓢'(ℂ,ℂ)) := by
    obtain ⟨w,hw,he⟩ := hF i 0
    simp only [Nat.cast_zero,sobolevInjection,neg_zero,besselPotential_zero,
      ContinuousLinearMap.id_comp,Lp.toTemperedDistributionCLM_apply] at he
    exact ⟨w,hw,he⟩
  choose W hW hWe using hF₀
  let rhs : P → Hilbert n := fun p => WithLp.toLp 2 (fun i => W i p)
  have hrhs : ContDiff ℝ (⊤ : ℕ∞) rhs :=
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
      (contDiff_pi.mpr hW)
  exact ⟨fun p i => F i p,rhs,(fun p i z => hFe i p z),(fun N i => hF i N),hrhs,
    fun p i => hWe i p⟩

/-- Dense-parameter supported weak solvability extends to all parameters in the
actual L2/distribution spaces, and the solution varies strongly smoothly. -/
theorem global_supported_of_dense {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
    (F : P → n → 𝓢(ℂ,ℂ)) (f : P → Hilbert n)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hFe : ∀ p i, entryInjection i (f p)=(F p i : 𝓢'(ℂ,ℂ)))
    {D : Set P} (hD : Dense D)
    (hex : ∀ p∈D, ∃ w : Hilbert n, ∀ i,
      planarOperator (fun i j z => a i j (p,z)) i w=entryInjection i (f p) ∧
      LocalEqual Sᶜ (entryInjection i w) 0) :
    ∃ u : P → Hilbert n, ContDiff ℝ (⊤ : ℕ∞) u ∧ ∀ p i,
      planarOperator (fun i j z => a i j (p,z)) i (u p)=entryInjection i (f p) ∧
      LocalEqual Sᶜ (entryInjection i (u p)) 0 := by
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) p).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  have hex' : ∀ p∈D, ∃ v : n → Test, (∀ i, tsupport (v i : ℂ → ℂ)⊆S) ∧
      ∀ i, planarOperator (fun i j z => a i j (p,z)) i (embed v)=entryInjection i (f p) := by
    intro p hp
    obtain ⟨w,hw⟩ := hex p hp
    obtain ⟨v,hv,hvs⟩ := supported_weak_is_test hS (fun i j z => a i j (p,z))
      (hat p) w (F p) (fun i => (hw i).1.trans (hFe p i)) (fun i => (hw i).2)
    exact ⟨v,hvs,fun i => by rw [hv]; exact (hw i).1⟩
  let Q : P → Set (Hilbert n) := fun p => {w | ∀ i,
    planarOperator (fun i j z => a i j (p,z)) i w=entryInjection i (f p) ∧
      LocalEqual Sᶜ (entryInjection i w) 0}
  have hconv : ∀ p, Convex ℝ (Q p) := by
    intro p u hu v hv b c _ _ hbc i
    have hh : (b : ℂ)+(c : ℂ)=1 := by exact_mod_cast hbc
    change planarOperator (fun i j z => a i j (p,z)) i
      ((b : ℂ) • u+(c : ℂ) • v)=_ ∧ _
    constructor
    · ext φ
      simp only [map_add,map_smul,(hu i).1,(hv i).1,add_apply,smul_apply,smul_eq_mul]
      rw [← add_mul,hh,one_mul]
    · intro φ hφ hφs
      change (entryInjection i ((b : ℂ) • u+(c : ℂ) • v)) φ=0
      simp only [map_add,map_smul,add_apply,smul_apply,(hu i).2 φ hφ hφs,
        (hv i).2 φ hφ hφs,zero_apply,smul_zero,add_zero]
  have hlocal : ∀ p : P, ∃ U ∈ nhds p, ∃ u : P → Hilbert n,
      ContMDiffOn 𝓘(ℝ,P) 𝓘(ℝ,Hilbert n) (⊤ : ℕ∞) u U ∧ ∀ t∈U, u t∈Q t := by
    intro p
    obtain ⟨U,u,hU,hp,hu,he⟩ := local_supported_of_dense_tests hS hK a ha hs f hf hD hex' p
    exact ⟨U,hU.mem_nhds hp,u,hu.contMDiffOn,he⟩
  obtain ⟨u,he⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ,P) hconv hlocal
  exact ⟨u,u.contMDiff.contDiff,he⟩
end ElasticityPlanar
namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
lemma smooth_operator_all_orders {K : Set ℂ} (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
    (w : P → Hilbert n) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (F : P → n → 𝓢(ℂ,ℂ))
    (hF : ∀ N : ℕ, ∀ i, SmoothSobolev N (fun p => (F p i : 𝓢'(ℂ,ℂ))))
    (he : ∀ p i, planarOperator (fun i j z => a i j (p,z)) i (w p)=(F p i : 𝓢'(ℂ,ℂ))) :
    ∀ N : ℕ, ∀ i, SmoothLocalSobolev univ N (fun p => entryInjection i (w p)) := by
  let u : P → n → 𝓢'(ℂ,ℂ) := fun p i => entryInjection i (w p)
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) p).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  have he' (p : P) (i : n) : LocalEqual univ (ElasticityPlanarDistribution.dbar (u p i))
      ((F p i : 𝓢'(ℂ,ℂ))+∑ j, smulLeftCLM ℂ (fun z => -(a i j (p,z))) (u p j)) := by
    intro φ _ _
    have h := congrArg (fun v : 𝓢'(ℂ,ℂ) => v φ) (he p i)
    rw [planarOperator_apply] at h
    have hn (j : n) : smulLeftCLM ℂ (fun z => -(a i j (p,z))) (u p j)=
        -smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j) := by
      change smulLeftCLM ℂ (-(fun z => a i j (p,z))) (u p j)=_
      rw [smulLeftCLM_neg (hat p i j),neg_apply]
    simp only [hn,Finset.sum_neg_distrib,add_apply,neg_apply] at h ⊢
    change ElasticityPlanarDistribution.dbar (u p i) φ+
      (∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j)) φ=(F p i : 𝓢'(ℂ,ℂ)) φ at h
    linear_combination h
  have hu (i : n) : SmoothLocalSobolev univ 0 (fun p => u p i) := by
    have hz : SmoothSobolev 0 (fun p => u p i) := by
      let L : Hilbert n →L[ℂ] PL2 := (ContinuousLinearMap.proj i).comp
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)).toContinuousLinearMap
      refine ⟨fun p => L (w p),(L.restrictScalars ℝ).contDiff.comp hw,fun p => ?_⟩
      simp only [sobolevInjection,neg_zero,besselPotential_zero,ContinuousLinearMap.id_comp,
        Lp.toTemperedDistributionCLM_apply]
      rfl
    simpa only [Nat.cast_zero] using (SmoothSobolev.local_nat (N := 0) (by simpa only [Nat.cast_zero] using hz) univ)
  exact ElasticityPlanarDistribution.smooth_variable_all_orders hK
    (fun i j q => -(a i j q)) (fun i j => (ha i j).neg)
    (fun i j p z hz => by rw [hs i j p z hz,neg_zero])
    u (fun p i => (F p i : 𝓢'(ℂ,ℂ))) he' hu (fun N i => (hF N i).local_nat univ)

lemma supported_smooth_test_family {S : Set ℂ} (hS : IsCompact S)
    (u : P → Lp ℂ 2 (volume : Measure ℂ))
    (hu : ∀ N : ℕ, SmoothLocalSobolev univ N (fun p => (u p : 𝓢'(ℂ,ℂ))))
    (hs : ∀ p, LocalEqual Sᶜ (u p : 𝓢'(ℂ,ℂ)) 0) :
    ∃ v : P → Test, ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 q.2) ∧
      ∀ p, L2 (v p)=u p ∧ tsupport (v p : ℂ → ℂ)⊆S := by
  obtain ⟨R,hR,hSR⟩ := hS.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : ℂ) := ⟨R,R+1,hR,by simp⟩
  let c : ContDiffBump (0 : ℂ) := ⟨R+3,R+4,by linarith,by linarith⟩
  have hc : HasCompactSupport (fun z : ℂ => (c z : ℂ)) :=
    c.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  have hcs : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (c z : ℂ)) := Complex.ofRealCLM.contDiff.comp c.contDiff
  have h1 : EqOn (fun z : ℂ => (c z : ℂ)) 1 (Metric.ball 0 (R+3)) := by
    intro z hz
    change (c z : ℂ)=1
    rw [c.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)]
    rfl
  obtain ⟨w,hw,hwe⟩ := SmoothLocalSobolev.joint_schwartz_representative
    (fun p => (u p : 𝓢'(ℂ,ℂ))) hu hcs hc (subset_univ _) h1
  have hb : HasCompactSupport (fun z : ℂ => (b z : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  let v : P → Test := fun p => ⟨fun z => (b z : ℂ)*w p z,
    ⟨(Complex.ofRealCLM.contDiff.comp b.contDiff).mul ((w p).smooth ⊤),hb.mul_right⟩⟩
  refine ⟨v,((Complex.ofRealCLM.contDiff.comp b.contDiff).comp contDiff_snd).mul hw,fun p => ?_⟩
  have hsch (p : P) : ((w p).toLp 2 (volume : Measure ℂ) : 𝓢'(ℂ,ℂ))=(w p : 𝓢'(ℂ,ℂ)) := by
    exact Lp.toTemperedDistribution_toLp_eq (w p)
  have hlocal : ∀ᵐ z : ℂ, z∈Metric.ball 0 (R+3) → u p z=w p z := by
    have he : LocalEqual (Metric.ball 0 (R+3)) (u p : 𝓢'(ℂ,ℂ))
        ((w p).toLp 2 (volume : Measure ℂ) : 𝓢'(ℂ,ℂ)) := by rw [hsch]; exact hwe p
    filter_upwards [he.lp_ae Metric.isOpen_ball (u p) ((w p).toLp 2 volume),
      (w p).coeFn_toLp 2 volume] with z h hzw using fun hz => (h hz).trans hzw
  have hs' : LocalEqual Sᶜ (u p : 𝓢'(ℂ,ℂ)) ((0 : Lp ℂ 2 (volume : Measure ℂ)) : 𝓢'(ℂ,ℂ)) := by
    change LocalEqual Sᶜ (u p : 𝓢'(ℂ,ℂ)) ((Lp.toTemperedDistributionCLM ℂ volume 2) 0)
    rw [map_zero]
    exact hs p
  have hzero := LocalEqual.lp_ae hS.isClosed.isOpen_compl (u p) 0 hs'
  have hev : L2 (v p)=u p := by
    apply Lp.ext
    filter_upwards [(toSchwartz (v p)).coeFn_toLp 2 volume,hlocal,hzero,Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz hzB hzout hz0
    change (L2 (v p) : ℂ → ℂ) z=v p z at hz
    rw [hz]
    change (b z : ℂ)*w p z=u p z
    by_cases hzS : z∈S
    · have hzn : ‖z‖≤R := hSR z hzS
      have hzB' : z∈Metric.ball 0 (R+3) := by simpa only [Metric.mem_ball,dist_zero_right] using (show ‖z‖<R+3 by linarith)
      have hzb : z∈Metric.closedBall 0 b.rIn := by simpa only [b,Metric.mem_closedBall,dist_zero_right] using hzn
      rw [b.one_of_mem_closedBall hzb,Complex.ofReal_one,one_mul]
      exact (hzB hzB').symm
    · have hu0 : u p z=0 := (hzout hzS).trans hz0
      rw [hu0]
      by_cases hzB' : z∈Metric.ball 0 (R+3)
      · rw [← hzB hzB',hu0,mul_zero]
      · have hn : R+3≤‖z‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hzB'
        rw [b.zero_of_le_dist (by change R+1≤dist z 0; rw [dist_zero_right]; linarith),Complex.ofReal_zero,zero_mul]
  refine ⟨hev,?_⟩
  have hveq : LocalEqual Sᶜ (toSchwartz (v p) : 𝓢'(ℂ,ℂ)) ((0 : 𝓢(ℂ,ℂ)) : 𝓢'(ℂ,ℂ)) := by
    rw [← L2_distribution,hev,map_zero]
    exact hs p
  have hpt := hveq.schwartz_eqOn hS.isClosed.isOpen_compl
  apply closure_minimal _ hS.isClosed
  intro z hz
  by_contra hzS
  exact hz (hpt hzS)
/-- The dense-parameter assertion uses genuine weak solutions, not an assumed
smooth selection. Compact support and the elliptic estimate construct the
unique jointly smooth selection. -/
theorem supported_parameter_inversion {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i p z, z∉K → f i (p,z)=0)
    {D : Set P} (hD : Dense D)
    (hex : ∀ p∈D, ∃ w : Hilbert n, ∀ i,
      planarOperator (fun i j z => a i j (p,z)) i w=
        (toSchwartz ⟨fun z => f i (p,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
          compact_slice hK (f i) (hfs i) p⟩⟩ : 𝓢'(ℂ,ℂ)) ∧
      LocalEqual Sᶜ (entryInjection i w) 0) :
    ∃ v : P → n → Test,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 i q.2)) ∧
      (∀ p i, tsupport (v p i : ℂ → ℂ)⊆S) ∧
      ∀ p i z, schwartzDbar (toSchwartz (v p i)) z+
        ∑ j, a i j (p,z)*v p j z=f i (p,z) := by
  obtain ⟨F,w,hFe,hF,hw,hwe⟩ := compact_smooth_source hK f hf hfs
  have hFt (p : P) (i : n) : F p i=toSchwartz
      ⟨fun z => f i (p,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
          compact_slice hK (f i) (hfs i) p⟩⟩ := by
    ext z
    exact hFe p i z
  have hex' : ∀ p∈D, ∃ u : Hilbert n, ∀ i,
      planarOperator (fun i j z => a i j (p,z)) i u=entryInjection i (w p) ∧
        LocalEqual Sᶜ (entryInjection i u) 0 := by
    intro p hp
    obtain ⟨u,hu⟩ := hex p hp
    exact ⟨u,fun i => ⟨by rw [hwe,hFt]; exact (hu i).1,(hu i).2⟩⟩
  obtain ⟨u,hu,he⟩ := global_supported_of_dense hS hK a ha hs F w hw hwe hD hex'
  have he' (p : P) (i : n) : planarOperator (fun i j z => a i j (p,z)) i (u p)=(F p i : 𝓢'(ℂ,ℂ)) :=
    (he p i).1.trans (hwe p i)
  have hall := smooth_operator_all_orders hK a ha hs u hu F hF he'
  choose v hv hve using fun i => supported_smooth_test_family hS (fun p => u p i)
    (fun N => hall N i) (fun p => (he p i).2)
  have hvu (p : P) : embed (fun i => v i p)=u p := PiLp.ext (fun i => (hve i p).1)
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) p).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  refine ⟨fun p i => v i p,hv,(fun p i => (hve i p).2),fun p i z => ?_⟩
  let q : Test := transport (fun i j z => a i j (p,z)) (fun i j => (hat p i j).1) (fun i => v i p) i
  have hq : (toSchwartz q : 𝓢'(ℂ,ℂ))=(F p i : 𝓢'(ℂ,ℂ)) := by
    rw [← L2_distribution]
    change entryInjection i (embed (transport (fun i j z => a i j (p,z))
      (fun i j => (hat p i j).1) (fun i => v i p)))=_
    rw [← planarOperator_test _ (hat p),hvu,he']
  have hp := (show LocalEqual univ (toSchwartz q : 𝓢'(ℂ,ℂ)) (F p i : 𝓢'(ℂ,ℂ)) from
    fun φ _ _ => congrArg (fun t : 𝓢'(ℂ,ℂ) => t φ) hq).schwartz_eqOn isOpen_univ (mem_univ z)
  have hqv : toSchwartz q=schwartzDbar (toSchwartz (v i p))+
      ∑ j, SchwartzMap.smulLeftCLM ℂ (fun z => a i j (p,z)) (toSchwartz (v j p)) := by
    simp only [q,transport,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_smul,map_sum,
      toSchwartz_d,schwartzDbar]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => toSchwartz_mul _ (hat p i j) (v j p))
  rw [hqv] at hp
  simpa only [add_apply,sum_apply,SchwartzMap.smulLeftCLM_apply_apply (hat p i _),
    smul_eq_mul,toSchwartz_apply,hFe] using hp

lemma supported_weak_unique {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u v : Hilbert n) (he : ∀ i, planarOperator a i u=planarOperator a i v)
    (hu : ∀ i, LocalEqual Sᶜ (entryInjection i u) 0)
    (hv : ∀ i, LocalEqual Sᶜ (entryInjection i v) 0) : u=v := by
  apply sub_eq_zero.mp
  apply supported_weak_kernel hS a ha (u-v)
  · intro i
    rw [map_sub,he,sub_self]
  · intro i φ hφ hs
    simp only [map_sub,sub_apply,hu i φ hφ hs,hv i φ hφ hs,sub_self,zero_apply]
end ElasticityPlanar
namespace ElasticityGeneralSlicing
open Set MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal LineDeriv Topology
open ElasticitySlicing
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar ElasticityRegularity
open ElasticityPlanarDistribution (Dist dbar)

lemma tests_determine_supported (S : Set ℂ) (hS : IsCompact S) (u w : PL2)
    (hsu : ∀ᵐ z : ℂ, z∉S → u z=0) (hsw : ∀ᵐ z : ℂ, z∉S → w z=0)
    (he : ∀ φ : Test, (∫ z, φ z*w z)=(∫ z, testDbar φ z*u z)) :
    dbar (u : Dist)+(w : Dist)=0 := by
  obtain ⟨χ,hχ,hc,_,hχ1,_⟩ := ElasticityBoundary.compact_smooth_cutoff hS isOpen_univ (subset_univ S)
  ext φ
  let ψ : Test := ⟨fun z => (χ z : ℂ)*φ z,⟨
    (Complex.ofRealCLM.contDiff.comp hχ).mul (φ.smooth ⊤),hc.comp_left Complex.ofReal_zero |>.mul_right⟩⟩
  have hg (z : ℂ) (hz : z∈S) : (ψ : ℂ → ℂ)=ᶠ[𝓝 z] (φ : ℂ → ℂ) := by
    filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet hz)] with y hy
    change (χ y : ℂ)*φ y=φ y
    simp only [hy,Complex.ofReal_one,one_mul]
  have hv (z : ℂ) (hz : z∈S) : ψ z=φ z := (hg z hz).eq_of_nhds
  have hd (z : ℂ) (hz : z∈S) : testDbar ψ z=schwartzDbar φ z := by
    change fderiv ℝ (ψ : ℂ → ℂ) z 1+Complex.I*fderiv ℝ (ψ : ℂ → ℂ) z Complex.I=
      fderiv ℝ (φ : ℂ → ℂ) z 1+Complex.I*fderiv ℝ (φ : ℂ → ℂ) z Complex.I
    rw [(hg z hz).fderiv_eq]
  have h1 : (∫ z, ψ z*w z)=(∫ z, φ z*w z) := by
    apply integral_congr_ae
    filter_upwards [hsw] with z hz
    by_cases hm : z∈S
    · rw [hv z hm]
    · rw [hz hm,mul_zero,mul_zero]
  have h2 : (∫ z, testDbar ψ z*u z)=(∫ z, schwartzDbar φ z*u z) := by
    apply integral_congr_ae
    filter_upwards [hsu] with z hz
    by_cases hm : z∈S
    · rw [hd z hm]
    · rw [hz hm,mul_zero,mul_zero]
  have hh := h1.symm.trans ((he ψ).trans h2)
  have hh' : (w : Dist) φ=(u : Dist) (schwartzDbar φ) := by
    simpa only [Lp.toTemperedDistribution_apply,smul_eq_mul] using hh
  simp only [dbar,schwartzDbar,add_apply,smul_apply,
    TemperedDistribution.lineDerivOp_apply_apply,map_neg,zero_apply,smul_eq_mul] at *
  rw [hh',map_add,map_smul]
  ring

lemma supported_local_zero (S : Set ℂ) (u : PL2)
    (hsu : ∀ᵐ z : ℂ, z∉S → u z=0) : LocalEqual Sᶜ (u : Dist) 0 := by
  intro φ _ hs
  rw [Lp.toTemperedDistribution_apply]
  change (∫ z, φ z*u z)=0
  apply integral_eq_zero_of_ae
  filter_upwards [hsu] with z hz
  by_cases hm : z∈S
  · have hn : z∉tsupport (φ : ℂ → ℂ) := fun hh => hs hh hm
    simp only [image_eq_zero_of_notMem_tsupport hn,zero_mul,Pi.zero_apply]
  · simp only [hz hm,mul_zero,Pi.zero_apply]

omit [BorelSpace P] in
/-- Compact support passes through Fubini and through the chosen L2 representative. -/
lemma supported_slice (S : Set ℂ) (u : P × ℂ → ℂ)
    (hu : MemLp u 2 volume) (hs : ∀ᵐ q : P × ℂ, q.2∉S → u q=0) :
    ∀ᵐ t : P, ∀ᵐ z : ℂ, z∉S → sliceLp u t z=0 := by
  have hu' := memLp_two_slices (ν := (volume : Measure P)) (κ := (volume : Measure ℂ)) hu
  have hs' := Measure.ae_ae_of_ae_prod hs
  filter_upwards [hu',hs'] with t hut hst
  filter_upwards [sliceLp_coe hut,hst] with z hz hsz
  intro h
  rw [hz,hsz h]

/-- The slicing result is an actual global planar distribution equation,
not merely equality on a selected family of test functions. -/
theorem cylinder_supported_slices (S : Set ℂ) (hS : IsCompact S)
    (u w : Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : Integrable (u : P × ℂ → ℂ)) (hw : Integrable (w : P × ℂ → ℂ))
    (hsu : ∀ᵐ q : P × ℂ, q.2∉S → u q=0) (hsw : ∀ᵐ q : P × ℂ, q.2∉S → w q=0)
    (he : ∂_{((0:P),(1:ℂ))} (u : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u : 𝓢'(P × ℂ,ℂ))+(w : 𝓢'(P × ℂ,ℂ))=0) :
    ∀ᵐ t : P,
      dbar (sliceLp u t : Dist)+(sliceLp w t : Dist)=0 ∧
      LocalEqual Sᶜ (sliceLp u t : Dist) 0 := by
  have he' := cylinder_weak_slices u w hu hw he
  have hsu' := supported_slice S u (Lp.memLp u) hsu
  have hsw' := supported_slice S w (Lp.memLp w) hsw
  filter_upwards [he',hsu',hsw'] with t ht hut hwt
  refine ⟨tests_determine_supported S hS (sliceLp u t) (sliceLp w t) hut hwt ?_,
    supported_local_zero S (sliceLp u t) hut⟩
  intro φ
  convert ht.2.2 φ using 1
  · apply integral_congr_ae
    filter_upwards [sliceLp_coe ht.2.1] with z hz
    rw [hz]
  · apply integral_congr_ae
    filter_upwards [sliceLp_coe ht.1] with z hz
    rw [hz]

end ElasticityGeneralSlicing
namespace ElasticityGeneralSlicing
open Set MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal BigOperators Topology LineDeriv
open ElasticitySlicing
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar ElasticityRegularity
open ElasticityPlanarDistribution (Dist dbar)
variable {n : Type*} [Fintype n]

lemma sliced_coefficients (a : n → ℂ → ℂ) (ha : ∀ j,(a j).HasTemperateGrowth)
    (u : n → PL2) (w : PL2) (f : Test)
    (he : ∀ᵐ z : ℂ, w z=∑ j,a j z*u j z-f z) :
    (w : Dist)=∑ j,smulLeftCLM ℂ (a j) (u j : Dist)-(toSchwartz f : Dist) := by
  classical
  ext φ
  have hi (j : n) : Integrable (fun z => φ z*(a j z*u j z)) := by
    have hh := ((SchwartzMap.smulLeftCLM ℂ (a j) φ).memLp 2 volume).integrable_mul (Lp.memLp (u j))
    convert hh using 1
    ext z
    simp only [Pi.mul_apply,SchwartzMap.smulLeftCLM_apply_apply (ha j),smul_eq_mul]
    ring
  have hf : Integrable (fun z => φ z*f z) :=
    (φ.memLp 2 volume).integrable_mul ((toSchwartz f).memLp 2 volume)
  have he' : (fun z => φ z*w z)=ᵐ[volume] fun z => (∑ j,φ z*(a j z*u j z))-φ z*f z := by
    filter_upwards [he] with z hz
    simp only [hz,mul_sub,Finset.mul_sum]
  simp only [Lp.toTemperedDistribution_apply,sub_apply,sum_apply,
    smulLeftCLM_apply_apply,SchwartzMap.coe_apply,smul_eq_mul]
  rw [integral_congr_ae he',integral_sub (integrable_finsetSum _ (fun j _ => hi j)) hf,
    integral_finsetSum _ (fun j _ => hi j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    change φ z*(a j z*u j z)=((SchwartzMap.smulLeftCLM ℂ (a j)) φ) z*u j z
    rw [SchwartzMap.smulLeftCLM_apply_apply (ha j)]
    simp only [smul_eq_mul]
    ring)

/-- Genuine cylinder weak solutions give supported weak planar solutions on a
single full-measure, hence dense, set of transverse parameters. -/
theorem coupled_slice_equations (S K : Set ℂ) (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j t z,z∉K → a i j (t,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i t z,z∉K → f i (t,z)=0)
    (u w : n → Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : ∀ i,Integrable (u i : P × ℂ → ℂ)) (hw : ∀ i,Integrable (w i : P × ℂ → ℂ))
    (hsu : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → u i q=0)
    (hsw : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → w i q=0)
    (hc : ∀ i,∀ᵐ q : P × ℂ,w i q=∑ j,a i j q*u j q-f i q)
    (he : ∀ i, ∂_{((0:P),(1:ℂ))} (u i : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u i : 𝓢'(P × ℂ,ℂ))+(w i : 𝓢'(P × ℂ,ℂ))=0) :
    ∀ᵐ t : P, ∀ i,
      planarOperator (fun i j z => a i j (t,z)) i
        (WithLp.toLp 2 (fun j => sliceLp (u j) t))=
        (toSchwartz ⟨fun z => f i (t,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
          compact_slice hK (f i) (hfs i) t⟩⟩ : Dist) ∧
      LocalEqual Sᶜ (sliceLp (u i) t : Dist) 0 := by
  classical
  have hsl : ∀ᵐ t : P, ∀ i,
      dbar (sliceLp (u i) t : Dist)+(sliceLp (w i) t : Dist)=0 ∧
      LocalEqual Sᶜ (sliceLp (u i) t : Dist) 0 := by
    rw [ae_all_iff]
    exact fun i => cylinder_supported_slices S hS (u i) (w i) (hu i) (hw i) (hsu i) (hsw i) (he i)
  have huc : ∀ᵐ t : P,∀ i, MemLp (fun z => u i (t,z)) 2 volume := by
    rw [ae_all_iff]
    exact fun i => memLp_two_slices (Lp.memLp (u i))
  have hwc : ∀ᵐ t : P,∀ i, MemLp (fun z => w i (t,z)) 2 volume := by
    rw [ae_all_iff]
    exact fun i => memLp_two_slices (Lp.memLp (w i))
  have hcc : ∀ᵐ t : P,∀ i,∀ᵐ z : ℂ,w i (t,z)=∑ j,a i j (t,z)*u j (t,z)-f i (t,z) := by
    rw [ae_all_iff]
    exact fun i => Measure.ae_ae_of_ae_prod (hc i)
  filter_upwards [hsl,huc,hwc,hcc] with t ht hut hwt hct
  intro i
  refine ⟨?_,(ht i).2⟩
  let ft : Test := ⟨fun z => f i (t,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
    compact_slice hK (f i) (hfs i) t⟩⟩
  have hac (j : n) : (fun z => a i j (t,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) t).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  have hrel : ∀ᵐ z : ℂ,sliceLp (w i) t z=∑ j,a i j (t,z)*sliceLp (u j) t z-ft z := by
    have huall : ∀ᵐ z : ℂ,∀ j,sliceLp (u j) t z=u j (t,z) := by
      rw [ae_all_iff]
      exact fun j => sliceLp_coe (hut j)
    filter_upwards [sliceLp_coe (hwt i),huall,hct i] with z hwz huz hcz
    simpa only [hwz,huz] using hcz
  have hh := sliced_coefficients (fun j z => a i j (t,z)) hac
    (fun j => sliceLp (u j) t) (sliceLp (w i) t) ft hrel
  have hz := (ht i).1
  rw [hh] at hz
  rw [planarOperator_apply]
  change dbar (sliceLp (u i) t : Dist)+∑ j,smulLeftCLM ℂ (fun z => a i j (t,z))
    (sliceLp (u j) t : Dist)=(toSchwartz ft : Dist)
  exact sub_eq_zero.mp (by simpa only [add_sub_assoc] using hz)

/-- Completion of the almost-every-plane to every-plane step. No smooth weak
representative or nowhere-exceptional slicing has been assumed. -/
theorem smooth_supported_of_cylinder (S K : Set ℂ) (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j t z,z∉K → a i j (t,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i t z,z∉K → f i (t,z)=0)
    (u w : n → Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : ∀ i,Integrable (u i : P × ℂ → ℂ)) (hw : ∀ i,Integrable (w i : P × ℂ → ℂ))
    (hsu : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → u i q=0)
    (hsw : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → w i q=0)
    (hc : ∀ i,∀ᵐ q : P × ℂ,w i q=∑ j,a i j q*u j q-f i q)
    (he : ∀ i, ∂_{((0:P),(1:ℂ))} (u i : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u i : 𝓢'(P × ℂ,ℂ))+(w i : 𝓢'(P × ℂ,ℂ))=0) :
    ∃ v : P → n → Test,
      (∀ i,ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 i q.2)) ∧
      (∀ t i,tsupport (v t i : ℂ → ℂ)⊆S) ∧
      ∀ t i z,schwartzDbar (toSchwartz (v t i)) z+∑ j,a i j (t,z)*v t j z=f i (t,z) := by
  have hh := coupled_slice_equations S K hS hK a ha hs f hf hfs u w hu hw hsu hsw hc he
  exact supported_parameter_inversion hS hK a ha hs f hf hfs (Measure.dense_of_ae hh)
    (fun t ht => ⟨WithLp.toLp 2 (fun i => sliceLp (u i) t),ht⟩)
end ElasticityGeneralSlicing
namespace ElasticityGeneralSlicing
open Set MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal BigOperators Topology LineDeriv
open ElasticitySlicing ElasticityPlanar ElasticityRegularity
open ElasticityPlanarDistribution (Dist dbar)
variable {n : Type*} [Fintype n]

lemma classical_planar_distribution (a : n → n → ℂ → ℂ)
    (ha : ∀ i j,(a i j).HasTemperateGrowth) (v : n → Test) (f : n → Test)
    (he : ∀ i z,schwartzDbar (toSchwartz (v i)) z+∑ j,a i j z*v j z=f i z) (i : n) :
    planarOperator a i (embed v)=(toSchwartz (f i) : Dist) := by
  rw [planarOperator_test a ha v i,entryInjection_apply,embed_apply,L2_distribution]
  congr 1
  ext z
  have ht : toSchwartz (transport a (fun i j => (ha i j).1) v i)=
      schwartzDbar (toSchwartz (v i))+∑ j,SchwartzMap.smulLeftCLM ℂ (a i j) (toSchwartz (v j)) := by
    simp only [transport,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_smul,map_sum,
      toSchwartz_d,schwartzDbar]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => toSchwartz_mul _ (ha i j) (v j))
  rw [ht]
  simpa only [add_apply,sum_apply,SchwartzMap.smulLeftCLM_apply_apply (ha i _),
    smul_eq_mul,toSchwartz_apply] using he i z

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]

/-- The jointly smooth solution is the actual weak cylinder solution, not an
unrelated branch. Supported uniqueness identifies it on almost every slice. -/
theorem smooth_cylinder_representative (S K : Set ℂ) (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j t z,z∉K → a i j (t,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i t z,z∉K → f i (t,z)=0)
    (u w : n → Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : ∀ i,Integrable (u i : P × ℂ → ℂ)) (hw : ∀ i,Integrable (w i : P × ℂ → ℂ))
    (hsu : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → u i q=0)
    (hsw : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → w i q=0)
    (hc : ∀ i,∀ᵐ q : P × ℂ,w i q=∑ j,a i j q*u j q-f i q)
    (he : ∀ i, ∂_{((0:P),(1:ℂ))} (u i : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u i : 𝓢'(P × ℂ,ℂ))+(w i : 𝓢'(P × ℂ,ℂ))=0) :
    ∃ v : P → n → Test,
      (∀ i,ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 i q.2)) ∧
      (∀ t i,tsupport (v t i : ℂ → ℂ)⊆S) ∧
      (∀ t i z,schwartzDbar (toSchwartz (v t i)) z+∑ j,a i j (t,z)*v t j z=f i (t,z)) ∧
      ∀ i,(u i : P × ℂ → ℂ)=ᵐ[volume] fun q => v q.1 i q.2 := by
  obtain ⟨v,hv,hvs,hve⟩ := smooth_supported_of_cylinder S K hS hK a ha hs f hf hfs
    u w hu hw hsu hsw hc he
  refine ⟨v,hv,hvs,hve,fun i => ?_⟩
  have hsl := coupled_slice_equations S K hS hK a ha hs f hf hfs u w hu hw hsu hsw hc he
  have hu' := memLp_two_slices (Lp.memLp (u i))
  have ha' (t i j) : (fun z => a i j (t,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) t).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  have hp (t i) : planarOperator (fun i j z => a i j (t,z)) i (embed (v t))=
      (toSchwartz ⟨fun z => f i (t,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
        compact_slice hK (f i) (hfs i) t⟩⟩ : Dist) :=
    classical_planar_distribution _ (ha' t) (v t)
      (fun i => ⟨fun z => f i (t,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
        compact_slice hK (f i) (hfs i) t⟩⟩) (hve t) i
  have hre : ∀ᵐ t : P,∀ᵐ z : ℂ,u i (t,z)=v t i z := by
    filter_upwards [hsl,hu'] with t ht hut
    have hh : (WithLp.toLp 2 (fun j => sliceLp (u j) t) : Hilbert n)=embed (v t) :=
      supported_weak_unique hS _ (ha' t) _ _ (fun j => (ht j).1.trans (hp t j).symm)
        (fun j => (ht j).2) (fun j => test_support_distribution (v t j) (hvs t j))
    have hi : sliceLp (u i) t=L2 (v t i) := congrArg (fun w : Hilbert n => w i) hh
    filter_upwards [sliceLp_coe hut,(toSchwartz (v t i)).coeFn_toLp 2 volume] with z hz hzv
    change L2 (v t i) z=v t i z at hzv
    exact hz.symm.trans ((congrArg (fun w : PL2 => w z) hi).trans hzv)
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr hre
  exact measurableSet_eq_fun (Lp.stronglyMeasurable (u i)).measurable (hv i).continuous.measurable

end ElasticityGeneralSlicing

end

end OAI
