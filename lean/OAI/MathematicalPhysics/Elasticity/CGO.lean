import OAI.MathematicalPhysics.Elasticity.ForcedTransport

namespace OAI

noncomputable section

namespace ElasticityAugmented
open Set
open scoped BigOperators
section Algebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)
lemma leadingR_add (θ : Fin 3 → ℂ) (lam m : A) (u v : Fin 3 → A) (b c : A) :
    leadingR D θ lam m (u+v) (b+c)=leadingR D θ lam m u b+leadingR D θ lam m v c :=
  (leadingRpair D θ lam m).map_add (u,b) (v,c)
lemma leadingS_add (θ : Fin 3 → ℂ) (lam m : A) (u v : Fin 3 → A) (b c : A) :
    leadingS D θ lam m (u+v) (b+c)=leadingS D θ lam m u b+leadingS D θ lam m v c := by
  simp only [leadingS,direction,Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib,mul_add]
  ring
lemma normal_add (θ : Fin 3 → ℂ) (u v : Fin 3 → A) : normal θ (u+v)=normal θ u+normal θ v :=
  (normalPair θ).map_add (u,0) (v,0)
end Algebra

def localAmp (U : Set X) (a : Amplitude Smooth) : Amplitude (LocalSmooth U) :=
  ((fun i => restrictSmooth U (a.1 i)),restrictSmooth U a.2)
def CompatibleOn {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (lam m : Smooth)
    (a : Amplitude Smooth) : Prop :=
  normal θ (R (localCoord hU) (restrictSmooth U lam) (restrictSmooth U m) (localAmp U a).1 (localAmp U a).2)=
    leadingP (localCoord hU) θ (restrictSmooth U m)
      (div (localCoord hU) (localAmp U a).1-(localAmp U a).2)

def RecursOn {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (lam m : Smooth)
    (a b : Amplitude Smooth) : Prop :=
  leadingR (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U m) (localAmp U b).1 (localAmp U b).2=
    -R (localCoord hU) (restrictSmooth U lam) (restrictSmooth U m) (localAmp U a).1 (localAmp U a).2 ∧
  leadingS (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U m) (localAmp U b).1 (localAmp U b).2=
    -S (localCoord hU) (restrictSmooth U lam) (restrictSmooth U m) (localAmp U a).1 (localAmp U a).2 ∧
  normal θ b.1=-(div coord a.1-a.2)

lemma recurs_compatible {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (lam m : Smooth)
    (a b : Amplitude Smooth) (h : RecursOn hU θ lam m a b) : CompatibleOn hU θ lam m b := by
  obtain ⟨hR,hS,hn⟩ := h
  apply recursive_normal_compatibility (localCoord hU) (localCoord_commute hU) θ
    (restrictSmooth U lam) (restrictSmooth U m) (localAmp U b).1 (localAmp U a).1
    (localAmp U b).2 (localAmp U a).2 hR hS
  have hh := congrArg (restrictSmooth U) hn
  simpa only [restrict_normal,map_neg,map_sub,restrict_div hU,localAmp] using hh

/-- One actual smooth recursive step, solving all three physical equations.
The open-region restriction algebra certifies differentiated compatibility;
continuity extends the tangent source to its compact closure for transport. -/
theorem exists_physical_recursion_step {U : Set X} (hU : IsOpen U) (hC : IsCompact (closure U))
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0)
    (a : Amplitude Smooth) (ha : CompatibleOn hU θ (k-r*r) (r*r) a) :
    ∃ b : Amplitude Smooth, RecursOn hU θ (k-r*r) (r*r) a b ∧
      CompatibleOn hU θ (k-r*r) (r*r) b := by
  obtain ⟨n,hn⟩ := exists_normalizing_vector θ hne
  let p : Fin 3 → Smooth := fun i => -(n i • (div coord a.1-a.2))
  let H : Fin 3 → Smooth := -R coord (k-r*r) (r*r) a.1 a.2-leadingR coord θ (k-r*r) (r*r) p 0
  let K : Smooth := -S coord (k-r*r) (r*r) a.1 a.2-leadingS coord θ (k-r*r) (r*r) p 0
  have hp (i) : restrictSmooth U (p i)=-(n i •
      (div (localCoord hU) (localAmp U a).1-(localAmp U a).2)) := by
    simp only [p,map_neg,map_smul,map_sub,restrict_div hU,localAmp]
  have ht : restrictSmooth U (normal θ H)=0 := by
    rw [restrict_normal]
    have hh := residual_source_tangent (localCoord hU) θ n hθ hn
      (restrictSmooth U (k-r*r)) (restrictSmooth U (r*r))
      (localAmp U a).1 (localAmp U a).2 ha
    simpa only [H,Pi.sub_apply,Pi.neg_apply,map_sub,map_neg,restrict_R hU,
      restrict_leadingR hU,map_zero,hp,localAmp,Pi.sub_def,Pi.neg_def] using hh
  have hH : ∀ x∈closure U,((normal θ H : Smooth) : X → ℂ) x=0 := by
    have he : EqOn ((normal θ H : Smooth) : X → ℂ) 0 U :=
      (restrictSmooth_zero_iff U _).mp ht
    exact he.closure (smooth_coe (normal θ H)).continuous continuous_const
  obtain ⟨u,b,hu,he⟩ := exists_physical_forced_transport θ hθ hne k r hr hk hl H K hC hH
  let c : Amplitude Smooth := (p+u,b)
  have hc : RecursOn hU θ (k-r*r) (r*r) a c := by
    refine ⟨?_,?_,?_⟩
    · funext i
      simp only [localAmp,Pi.neg_apply]
      rw [← restrict_leadingR hU,← restrict_R hU,← map_neg]
      apply (restrictSmooth_eq_iff U _ _).mpr
      intro x hx
      have hh := (he x (subset_closure hx)).1 i
      have hadd := congrArg (fun v : Fin 3 → Smooth => (v i : X → ℂ) x)
        (leadingR_add coord θ (k-r*r) (r*r) p u 0 b)
      simp only [zero_add] at hadd
      change ((leadingR coord θ (k-r*r) (r*r) (p+u) b i : Smooth) : X → ℂ) x=
        -((R coord (k-r*r) (r*r) a.1 a.2 i : Smooth) : X → ℂ) x
      change ((leadingR coord θ (k-r*r) (r*r) (p+u) b i : Smooth) : X → ℂ) x=
        ((leadingR coord θ (k-r*r) (r*r) p 0 i : Smooth) : X → ℂ) x+
          ((leadingR coord θ (k-r*r) (r*r) u b i : Smooth) : X → ℂ) x at hadd
      change ((leadingR coord θ (k-r*r) (r*r) u b i : Smooth) : X → ℂ) x=
        -((R coord (k-r*r) (r*r) a.1 a.2 i : Smooth) : X → ℂ) x-
          ((leadingR coord θ (k-r*r) (r*r) p 0 i : Smooth) : X → ℂ) x at hh
      linear_combination hadd+hh
    · simp only [localAmp]
      rw [← restrict_leadingS hU,← restrict_S hU,← map_neg]
      apply (restrictSmooth_eq_iff U _ _).mpr
      intro x hx
      have hh := (he x (subset_closure hx)).2
      have hadd := congrArg (fun v : Smooth => (v : X → ℂ) x)
        (leadingS_add coord θ (k-r*r) (r*r) p u 0 b)
      simp only [zero_add] at hadd
      change ((leadingS coord θ (k-r*r) (r*r) (p+u) b : Smooth) : X → ℂ) x=
        -((S coord (k-r*r) (r*r) a.1 a.2 : Smooth) : X → ℂ) x
      change ((leadingS coord θ (k-r*r) (r*r) (p+u) b : Smooth) : X → ℂ) x=
        ((leadingS coord θ (k-r*r) (r*r) p 0 : Smooth) : X → ℂ) x+
          ((leadingS coord θ (k-r*r) (r*r) u b : Smooth) : X → ℂ) x at hadd
      change ((leadingS coord θ (k-r*r) (r*r) u b : Smooth) : X → ℂ) x=
        -((S coord (k-r*r) (r*r) a.1 a.2 : Smooth) : X → ℂ) x-
          ((leadingS coord θ (k-r*r) (r*r) p 0 : Smooth) : X → ℂ) x at hh
      linear_combination hadd+hh
    · change normal θ (p+u)=_
      rw [normal_add,hu,add_zero]
      exact normal_particular θ n hn _
  exact ⟨c,hc,recurs_compatible hU θ (k-r*r) (r*r) a c hc⟩
end ElasticityAugmented
section
open Set
open scoped BigOperators
namespace ElasticityAugmented

/-- Every compatible smooth amplitude has an actual infinite recursive sequence;
only its finite truncations are used. There is no formal-solvability hypothesis. -/
theorem exists_recursive_series {U : Set X} (hU : IsOpen U) (hC : IsCompact (closure U))
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0)
    (a₀ : Amplitude Smooth) (ha₀ : CompatibleOn hU θ (k-r*r) (r*r) a₀) :
    ∃ a : ℕ → Amplitude Smooth, a 0=a₀ ∧
      (∀ j,RecursOn hU θ (k-r*r) (r*r) (a j) (a (j+1))) ∧
      ∀ j,CompatibleOn hU θ (k-r*r) (r*r) (a j) := by
  let E := {a : Amplitude Smooth // CompatibleOn hU θ (k-r*r) (r*r) a}
  have hex (a : E) := exists_physical_recursion_step hU hC θ hθ hne k r hr hk hl a.val a.property
  let step : E → E := fun a => ⟨Classical.choose (hex a),(Classical.choose_spec (hex a)).2⟩
  have hstep (a : E) : RecursOn hU θ (k-r*r) (r*r) a.val (step a).val :=
    (Classical.choose_spec (hex a)).1
  let seq : ℕ → E := Nat.rec ⟨a₀,ha₀⟩ (fun _ a => step a)
  refine ⟨fun j => (seq j).val,rfl,?_,fun j => (seq j).property⟩
  intro j
  exact hstep (seq j)

/-- The given genuine leading frame develops to physical compatible amplitudes,
with all three recursive equations on the same open region. -/
theorem exists_physical_formal_frame {U : Set X} (hU : IsOpen U) (hC : IsCompact (closure U))
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    ∃ a : Fin 3 → ℕ → Amplitude Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ ν,normal θ (a ν 0).1=0) ∧
      (∀ ν,leadingR (localCoord hU) θ (restrictSmooth U (k-r*r)) (restrictSmooth U (r*r))
          (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0 ∧
        leadingS (localCoord hU) θ (restrictSmooth U (k-r*r)) (restrictSmooth U (r*r))
          (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0) ∧
      (∀ ν j,RecursOn hU θ (k-r*r) (r*r) (a ν j) (a ν (j+1))) ∧
      ∀ ν x, ((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (changeP r (a ν 0).1 i : X → ℂ) x),
          (changeS k r hr (a ν 0).1 (a ν 0).2 : X → ℂ) x) := by
  obtain ⟨a₀,b₀,B,hn₀,he₀,hB⟩ := exists_physical_leading_frame θ hθ hne k r hr hk hl hC
  have hR₀ (ν) : leadingR (localCoord hU) θ (restrictSmooth U (k-r*r)) (restrictSmooth U (r*r))
      (localAmp U (a₀ ν,b₀ ν)).1 (localAmp U (a₀ ν,b₀ ν)).2=0 := by
    funext i
    simp only [localAmp,Pi.zero_apply]
    rw [← restrict_leadingR hU]
    exact (restrictSmooth_zero_iff U _).mpr (fun x hx => (he₀ ν x (subset_closure hx)).1 i)
  have hS₀ (ν) : leadingS (localCoord hU) θ (restrictSmooth U (k-r*r)) (restrictSmooth U (r*r))
      (localAmp U (a₀ ν,b₀ ν)).1 (localAmp U (a₀ ν,b₀ ν)).2=0 := by
    simp only [localAmp]
    rw [← restrict_leadingS hU]
    exact (restrictSmooth_zero_iff U _).mpr (fun x hx => (he₀ ν x (subset_closure hx)).2)
  have hc₀ (ν) : CompatibleOn hU θ (k-r*r) (r*r) (a₀ ν,b₀ ν) := by
    apply leading_stage_compatibility (localCoord hU) (localCoord_commute hU) θ _ _
      (localAmp U (a₀ ν,b₀ ν)).1 (localAmp U (a₀ ν,b₀ ν)).2 (hR₀ ν) (hS₀ ν)
    change normal θ (fun i => restrictSmooth U (a₀ ν i))=0
    rw [← restrict_normal,hn₀ ν,map_zero]
  choose a ha hrec hc using (fun ν => exists_recursive_series hU hC θ hθ hne k r hr hk hl (a₀ ν,b₀ ν) (hc₀ ν))
  refine ⟨a,B,?_,?_,hrec,?_⟩
  · intro ν
    rw [ha ν]
    exact hn₀ ν
  · intro ν
    rw [ha ν]
    exact ⟨hR₀ ν,hS₀ ν⟩
  · intro ν x
    rw [ha ν]
    exact hB ν x
end ElasticityAugmented

end
namespace ElasticityAugmented
open Set
open scoped BigOperators

def localAmpLM (U : Set X) : Amplitude Smooth →ₗ[ℂ] Amplitude (LocalSmooth U) where
  toFun := localAmp U
  map_add' a b := by ext i <;> simp [localAmp,map_add]
  map_smul' c a := by ext i <;> simp [localAmp,map_smul]
lemma localAmp_truncation (U : Set X) (h : ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth) :
    localAmp U (truncation h N a)=truncation h N (fun j => localAmp U (a j)) := by
  exact map_sum (localAmpLM U) _ _ |>.trans (by simp only [map_smul]; rfl)
lemma restrict_shifted {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (i : Fin 3) (f : Smooth) :
    restrictSmooth U (shifted coord z i f)=shifted (localCoord hU) z i (restrictSmooth U f) := by
  simp only [shifted_apply,map_add,map_smul,localCoord_restrict]
lemma restrict_LT {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (lam m : Smooth)
    (a : Fin 3 → Smooth) (i : Fin 3) :
    restrictSmooth U (LT (shifted coord z) lam m a i)=
      LT (shifted (localCoord hU) z) (restrictSmooth U lam) (restrictSmooth U m)
        (fun j => restrictSmooth U (a j)) i := by
  simp only [LT,divT,restrict_shifted hU,map_mul,map_sum,map_add]

/-- Literal finite physical residual on an open region. All compatibility
identities are local equalities, not strengthened global transport hypotheses. -/
theorem physical_truncation_residual_on {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (lam m : Smooth)
    (h : ℂ) (hh : h≠0) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (hR₀ : leadingR (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U m)
      (localAmp U (a 0)).1 (localAmp U (a 0)).2=0)
    (hn₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,RecursOn hU θ lam m (a j) (a (j+1))) (i : Fin 3) :
    EqOn ((LT (shifted coord (h⁻¹ • θ)) lam m (truncation h N a).1 i : Smooth) : X → ℂ)
      ((h^N • (R coord lam m (a N).1 (a N).2 i+
        (lam+m)*coord i (div coord (a N).1-(a N).2)+
        coord i lam*(div coord (a N).1-(a N).2)+
        (h⁻¹*θ i) • ((lam+m)*(div coord (a N).1-(a N).2))) : Smooth) : X → ℂ) U := by
  have hn₀' : normal θ (localAmp U (a 0)).1=0 := by
    simp only [localAmp,← restrict_normal,hn₀,map_zero]
  have hnrec (j) (hj : j<N) : normal θ (localAmp U (a (j+1))).1=
      -(div (localCoord hU) (localAmp U (a j)).1-(localAmp U (a j)).2) := by
    have hh := congrArg (restrictSmooth U) (hrec j hj).2.2
    simpa only [restrict_normal,map_neg,map_sub,restrict_div hU,localAmp] using hh
  have hhres := truncated_physical_residual (localCoord hU) (localCoord_commute hU) θ hθ
    (restrictSmooth U lam) (restrictSmooth U m) h hh N (fun j => localAmp U (a j))
    hR₀ (fun j hj => (hrec j hj).1) hn₀' hnrec i
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [restrict_LT hU]
  change LT (shifted (localCoord hU) (h⁻¹ • θ)) (restrictSmooth U lam) (restrictSmooth U m)
    (localAmp U (truncation h N a)).1 i=_
  rw [localAmp_truncation,hhres]
  simp only [map_smul,map_add,map_mul,map_sub,restrict_R hU,localCoord_restrict,restrict_div hU,localAmp]
  rw [← restrict_div hU,localCoord_restrict]
end ElasticityAugmented
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma exists_bounded_integer_multiplier (k : ℤ) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection (k : ℝ) (L f)=smulLeftCLM ℂ g (sobolevInjection (k : ℝ) f) := by
  cases k with
  | ofNat n => exact exists_bounded_nat_multiplier n hg hc
  | negSucc n =>
    simpa only [Int.cast_negSucc,Nat.cast_add,Nat.cast_one] using
      exists_bounded_negative_multiplier (n+1) hg hc

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma nested_multiplier {g η : E → ℂ} (hg : g.HasTemperateGrowth)
    (hη : η.HasTemperateGrowth) (h1 : Set.EqOn η 1 (tsupport g)) (u : 𝓢'(E,ℂ)) :
    smulLeftCLM ℂ g (smulLeftCLM ℂ η u)=smulLeftCLM ℂ g u := by
  have he : η*g=g := by
    ext x
    change η x*g x=g x
    by_cases hx : x ∈ tsupport g
    · rw [h1 hx]
      simp only [Pi.one_apply,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero]
  rw [smulLeftCLM_smulLeftCLM_apply hη hg,he]

omit [MeasurableSpace E] [BorelSpace E] in
lemma laplacian_product_divergence {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (u : 𝓢'(E,ℂ)) :
    Δ (smulLeftCLM ℂ g u)=smulLeftCLM ℂ g (Δ u)+
      ∑ i, ((2 : ℂ) • ∂_{b i} (smulLeftCLM ℂ (fun x => fderiv ℝ g x (b i)) u)-
        smulLeftCLM ℂ (fun x => fderiv ℝ (fun y => fderiv ℝ g y (b i)) x (b i)) u) := by
  rw [laplacian_product b hg hc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hgd := smooth_derivative hg (b i)
  have hcd := compact_derivative hc (b i)
  rw [distribution_leibniz (hcd.hasTemperateGrowth hgd) _
    ((compact_derivative hcd (b i)).hasTemperateGrowth (smooth_derivative hgd (b i)))]
  module

/-- A nested-cutoff interior norm estimate for the genuine distributional
Laplacian. All multiplier and derivative constants are produced by previously
proved closed graph arguments. The result includes the initial negative order. -/
theorem quantitative_cutoff_gain (k : ℤ) {χ η : E → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (h1 : Set.EqOn η 1 (tsupport χ)) :
    ∃ C : ℝ, 0<C ∧ ∀ (u : 𝓢'(E,ℂ)) (f g : Lp ℂ 2 (volume : Measure E)),
      sobolevInjection (k : ℝ) f=smulLeftCLM ℂ η u →
      sobolevInjection ((k : ℝ)-1) g=smulLeftCLM ℂ η (Δ u) →
      ∃ q : Lp ℂ 2 (volume : Measure E),
        sobolevInjection ((k : ℝ)+1) q=smulLeftCLM ℂ χ u ∧
        ‖q‖ ≤ C*(‖f‖+‖g‖) := by
  let b := stdOrthonormalBasis ℝ E
  let s : ℝ := k
  let H := Lp ℂ 2 (volume : Measure E)
  obtain ⟨M,hM⟩ := exists_bounded_integer_multiplier k hχ hcχ
  obtain ⟨N,hN⟩ := exists_bounded_integer_multiplier (k-1) hχ hcχ
  simp only [Int.cast_sub,Int.cast_one] at hN
  obtain ⟨J,hJ⟩ := exists_bounded_sobolev_inclusion (E := E) (show s-1 ≤ s by linarith)
  have hd (i : Fin (Module.finrank ℝ E)) := exists_bounded_sobolev_derivative s (b i)
  choose D hD using hd
  have hm (i : Fin (Module.finrank ℝ E)) := exists_bounded_integer_multiplier k
    (smooth_derivative hχ (b i)) (compact_derivative hcχ (b i))
  choose M₁ hM₁ using hm
  have hm₂ (i : Fin (Module.finrank ℝ E)) := exists_bounded_integer_multiplier k
    (smooth_derivative (smooth_derivative hχ (b i)) (b i))
    (compact_derivative (compact_derivative hcχ (b i)) (b i))
  choose M₂ hM₂ using hm₂
  let A : H →L[ℂ] H := ∑ i, ((2 : ℂ) • ((D i).comp (M₁ i))-J.comp (M₂ i))
  have hA (f : H) : sobolevInjection (s-1) (A f)=
      ∑ i, ((2 : ℂ) • ∂_{b i} (smulLeftCLM ℂ (fun x => fderiv ℝ χ x (b i)) (sobolevInjection s f))-
        smulLeftCLM ℂ (fun x => fderiv ℝ (fun y => fderiv ℝ χ y (b i)) x (b i)) (sobolevInjection s f)) := by
    dsimp only [s] at hD hJ ⊢
    simp only [A,sum_apply,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
      map_sum,map_sub,map_smul,hD,hJ,hM₁,hM₂]
  obtain ⟨K,hK,hgain⟩ := quantitative_laplacian_gain (E := E) s
  refine ⟨K*(‖M‖+‖N‖+‖A‖+1),by positivity,fun u f g hf hg => ?_⟩
  have hMf : sobolevInjection s (M f)=smulLeftCLM ℂ χ u := by
    rw [hM,hf]
    exact nested_multiplier (hcχ.hasTemperateGrowth hχ) (hcη.hasTemperateGrowth hη) h1 u
  have hsource : sobolevInjection (s-1) (N g+A f)=Δ (smulLeftCLM ℂ χ u) := by
    rw [map_add,hN,hg,hA,hf,laplacian_product_divergence b hχ hcχ]
    rw [nested_multiplier (hcχ.hasTemperateGrowth hχ) (hcη.hasTemperateGrowth hη) h1]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hdi := smooth_derivative hχ (b i)
    have hcdi := compact_derivative hcχ (b i)
    rw [nested_multiplier (hcdi.hasTemperateGrowth hdi) (hcη.hasTemperateGrowth hη)
      (fun x hx => h1 ((derivative_support_subset χ (b i)) hx)),
      nested_multiplier ((compact_derivative hcdi (b i)).hasTemperateGrowth (smooth_derivative hdi (b i)))
        (hcη.hasTemperateGrowth hη)
        (fun x hx => h1 ((derivative_support_subset χ (b i))
          ((derivative_support_subset _ (b i)) hx)))]
  obtain ⟨q,hq,hqn⟩ := hgain (M f) (N g+A f) (hMf ▸ hsource.symm)
  refine ⟨q,hq.trans hMf,hqn.trans ?_⟩
  have hMn := M.le_opNorm f
  have hNn := N.le_opNorm g
  have hAn := A.le_opNorm f
  have hsumn := norm_add_le (N g) (A f)
  have hsum : ‖M f‖+‖N g+A f‖ ≤ (‖M‖+‖N‖+‖A‖+1)*(‖f‖+‖g‖) := by
    have hNN := mul_nonneg (norm_nonneg N) (norm_nonneg f)
    have hMM := mul_nonneg (norm_nonneg M) (norm_nonneg g)
    have hAA := mul_nonneg (norm_nonneg A) (norm_nonneg g)
    nlinarith [norm_nonneg f,norm_nonneg g]
  calc
    K*(‖M f‖+‖N g+A f‖) ≤ K*((‖M‖+‖N‖+‖A‖+1)*(‖f‖+‖g‖)) := mul_le_mul_of_nonneg_left hsum hK.le
    _ = _ := by ring
end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A genuine localized first derivative has a bounded realization from the
larger cutoff's Sobolev data. This also holds at negative integers. -/
theorem exists_localized_derivative (k : ℤ) {a η : E → ℂ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hca : HasCompactSupport a)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (h1 : Set.EqOn η 1 (tsupport a)) (v : E) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ u f, sobolevInjection (k : ℝ) f=smulLeftCLM ℂ η u →
        sobolevInjection ((k : ℝ)-1) (L f)=smulLeftCLM ℂ a (∂_{v} u) := by
  obtain ⟨M,hM⟩ := exists_bounded_integer_multiplier k ha hca
  obtain ⟨D,hD⟩ := exists_bounded_sobolev_derivative (k : ℝ) v
  obtain ⟨J,hJ⟩ := exists_bounded_sobolev_inclusion (E := E) (show (k : ℝ)-1 ≤ k by linarith)
  obtain ⟨N,hN⟩ := exists_bounded_integer_multiplier k (smooth_derivative ha v)
    (compact_derivative hca v)
  refine ⟨D.comp M-J.comp N,fun u f hf => ?_⟩
  simp only [sub_apply,ContinuousLinearMap.comp_apply,map_sub,hD,hM,hJ,hN,hf]
  rw [nested_multiplier (hca.hasTemperateGrowth ha) (hcη.hasTemperateGrowth hη) h1,
    nested_multiplier ((compact_derivative hca v).hasTemperateGrowth (smooth_derivative ha v))
      (hcη.hasTemperateGrowth hη) (fun x hx => h1 ((derivative_support_subset a v) hx)),
    distribution_leibniz (hca.hasTemperateGrowth ha) v
      ((compact_derivative hca v).hasTemperateGrowth (smooth_derivative ha v))]
  module

/-- A bounded zeroth-order realization with one order of harmless loss. -/
theorem exists_localized_multiplier (k : ℤ) {a η : E → ℂ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hca : HasCompactSupport a)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (h1 : Set.EqOn η 1 (tsupport a)) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ u f, sobolevInjection (k : ℝ) f=smulLeftCLM ℂ η u →
        sobolevInjection ((k : ℝ)-1) (L f)=smulLeftCLM ℂ a u := by
  obtain ⟨M,hM⟩ := exists_bounded_integer_multiplier k ha hca
  obtain ⟨J,hJ⟩ := exists_bounded_sobolev_inclusion (E := E) (show (k : ℝ)-1 ≤ k by linarith)
  refine ⟨J.comp M,fun u f hf => ?_⟩
  simp only [ContinuousLinearMap.comp_apply,hJ,hM,hf]
  exact nested_multiplier (hca.hasTemperateGrowth ha) (hcη.hasTemperateGrowth hη) h1 u

end ElasticityRegularity
section
open scoped BigOperators
namespace ElasticityRegularity
/-- The precise polynomial loss for the shifted scalar-principal system. -/
theorem quadratic_parameter_norm {W ι : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [Fintype ι] (R₀ R₂ : W) (R₁ : ι → W) :
    ∃ C : ℝ, 0<C ∧ ∀ z : ι → ℂ,
      ‖R₀+(∑ i, z i • R₁ i)+(∑ i, z i*z i) • R₂‖ ≤ C*(1+∑ i, ‖z i‖)^2 := by
  classical
  let S := ∑ i, ‖R₁ i‖
  refine ⟨‖R₀‖+S+‖R₂‖+1,by dsimp [S]; positivity,fun z => ?_⟩
  let Z := ∑ i, ‖z i‖
  have hZ : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hz (i : ι) : ‖z i‖≤Z := Finset.single_le_sum (fun j _ => norm_nonneg (z j)) (Finset.mem_univ i)
  have hr (i : ι) : ‖R₁ i‖≤S := Finset.single_le_sum (fun j _ => norm_nonneg (R₁ j)) (Finset.mem_univ i)
  have hlin : ‖∑ i, z i • R₁ i‖ ≤ Z*S := by
    calc
      ‖∑ i, z i • R₁ i‖ ≤ ∑ i, ‖z i • R₁ i‖ := norm_sum_le _ _
      _ = ∑ i, ‖z i‖*‖R₁ i‖ := by simp only [norm_smul]
      _ ≤ ∑ i, ‖z i‖*S := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hr i) (norm_nonneg _))
      _ = Z*S := (Finset.sum_mul _ _ _).symm
  have hquad : ‖∑ i, z i*z i‖ ≤ Z^2 := by
    calc
      ‖∑ i, z i*z i‖ ≤ ∑ i, ‖z i*z i‖ := norm_sum_le _ _
      _ = ∑ i, ‖z i‖*‖z i‖ := by simp only [norm_mul]
      _ ≤ ∑ i, ‖z i‖*Z := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _))
      _ = Z^2 := by rw [← Finset.sum_mul]; change Z*Z=Z^2; ring
  have hn : ‖R₀+(∑ i, z i • R₁ i)+(∑ i, z i*z i) • R₂‖ ≤ ‖R₀‖+Z*S+Z^2*‖R₂‖ := by
    calc
      _ ≤ ‖R₀+(∑ i, z i • R₁ i)‖+‖(∑ i, z i*z i) • R₂‖ := norm_add_le _ _
      _ ≤ ‖R₀‖+Z*S+Z^2*‖R₂‖ := by
        rw [norm_smul]
        exact add_le_add ((norm_add_le _ _).trans (add_le_add_right hlin _))
          (mul_le_mul_of_nonneg_right hquad (norm_nonneg _))
  apply hn.trans
  change ‖R₀‖+Z*S+Z^2*‖R₂‖ ≤ (‖R₀‖+S+‖R₂‖+1)*(1+Z)^2
  have hW : 1 ≤ (1+Z)^2 := by nlinarith
  have hL : Z ≤ (1+Z)^2 := by nlinarith
  have hQ : Z^2 ≤ (1+Z)^2 := by nlinarith
  calc
    _ ≤ ‖R₀‖*(1+Z)^2+S*(1+Z)^2+‖R₂‖*(1+Z)^2 := by
      have h₀ := mul_le_mul_of_nonneg_left hW (norm_nonneg R₀)
      have h₁ := mul_le_mul_of_nonneg_left hL hS
      have h₂ := mul_le_mul_of_nonneg_left hQ (norm_nonneg R₂)
      nlinarith
    _ ≤ _ := by nlinarith [sq_nonneg (1+Z)]
end ElasticityRegularity

end
namespace ElasticityDistribution
open MeasureTheory TemperedDistribution

section
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityAugmented ElasticityRegularity
abbrev H := Lp ℂ 2 (volume : Measure X)
abbrev HV := Fin 4 → H

def lowerPart (z : Fin 3 → ℂ) (A : Fin 3 → Fin 4 → Fin 4 → Coeff)
    (V : Fin 4 → Fin 4 → Coeff) (U : Fin 4 → Dist) (i : Fin 4) : Dist :=
  (∑ k, ∑ j, A k i j • sd z k (U j))+(∑ j, V i j • U j)+
    (∑ k, (2*z k) • dd k (U i))+(∑ k, z k*z k) • U i

lemma cutoff_coeff {η : X → ℂ} (hη : η.HasTemperateGrowth) (a : Coeff) (u : Dist) :
    smulLeftCLM ℂ η (a • u)=smulLeftCLM ℂ (η*eval a) u := by
  rw [smul_def,smulLeftCLM_smulLeftCLM_apply (growth a) hη,mul_comm]

lemma coeff_complex_smul (a : Coeff) (c : ℂ) (u : Dist) : a • (c • u)=c • (a • u) :=
  (smul_comm c a u).symm

/-- The actual lower-order shifted augmented operator, localized on a smaller
cutoff, is polynomial in the phase with bounded Sobolev coefficients. -/
theorem exists_lower_realization (k : ℤ) {η ξ : X → ℂ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hcξ : HasCompactSupport ξ)
    (h1 : Set.EqOn ξ 1 (tsupport η))
    (A : Fin 3 → Fin 4 → Fin 4 → Coeff) (V : Fin 4 → Fin 4 → Coeff) (i : Fin 4) :
    ∃ L₀ L₂ : HV →L[ℂ] H, ∃ L₁ : Fin 3 → HV →L[ℂ] H,
      ∀ (z : Fin 3 → ℂ) (U : Fin 4 → Dist) (f : HV),
        (∀ j, sobolevInjection (k : ℝ) (f j)=smulLeftCLM ℂ ξ (U j)) →
        sobolevInjection ((k : ℝ)-1)
          ((L₀+(∑ d, z d • L₁ d)+(∑ d, z d*z d) • L₂) f)=
            smulLeftCLM ℂ η (lowerPart z A V U i) := by
  have hmA (d : Fin 3) (j : Fin 4) := exists_localized_multiplier k
    (hη.mul (eval_smooth (A d i j))) hcη.mul_right hξ hcξ
    (fun x hx => h1 (tsupport_mul_subset_left hx))
  choose M hM using hmA
  have hdA (d : Fin 3) (j : Fin 4) := exists_localized_derivative k
    (hη.mul (eval_smooth (A d i j))) hcη.mul_right hξ hcξ
    (fun x hx => h1 (tsupport_mul_subset_left hx)) (e d)
  choose D hD using hdA
  have hmV (j : Fin 4) := exists_localized_multiplier k
    (hη.mul (eval_smooth (V i j))) hcη.mul_right hξ hcξ
    (fun x hx => h1 (tsupport_mul_subset_left hx))
  choose N hN using hmV
  have hdη (d : Fin 3) := exists_localized_derivative k hη hcη hξ hcξ h1 (e d)
  choose T hT using hdη
  obtain ⟨J,hJ⟩ := exists_localized_multiplier k hη hcη hξ hcξ h1
  let pr (j : Fin 4) : HV →L[ℂ] H := ContinuousLinearMap.proj j
  let L₀ : HV →L[ℂ] H := (∑ d, ∑ j, (D d j).comp (pr j))+(∑ j, (N j).comp (pr j))
  let L₁ (d : Fin 3) : HV →L[ℂ] H := (∑ j, (M d j).comp (pr j))+(2 : ℂ) • (T d).comp (pr i)
  let L₂ : HV →L[ℂ] H := J.comp (pr i)
  refine ⟨L₀,L₂,L₁,fun z U f hf => ?_⟩
  have hM' (d : Fin 3) (j : Fin 4) := hM d j (U j) (f j) (hf j)
  have hD' (d : Fin 3) (j : Fin 4) := hD d j (U j) (f j) (hf j)
  have hN' (j : Fin 4) := hN j (U j) (f j) (hf j)
  have hT' (d : Fin 3) := hT d (U i) (f i) (hf i)
  have hJ' := hJ (U i) (f i) (hf i)
  simp only [L₀,L₁,L₂,pr,lowerPart,add_apply,sum_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,map_add,map_sum,map_smul,
    hM',hD',hN',hT',hJ',sd_apply,smul_add,cutoff_coeff (hcη.hasTemperateGrowth hη),
    Finset.sum_add_distrib,Finset.smul_sum,← smul_smul,dd_apply]
  simp only [smul_smul,mul_comm,Pi.mul_def]
  abel

/-- A fixed quadratic phase loss, with no elliptic estimate assumed. -/
theorem lower_realization_bound (k : ℤ) {η ξ : X → ℂ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hcξ : HasCompactSupport ξ)
    (h1 : Set.EqOn ξ 1 (tsupport η))
    (A : Fin 3 → Fin 4 → Fin 4 → Coeff) (V : Fin 4 → Fin 4 → Coeff) (i : Fin 4) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (U : Fin 4 → Dist) (f : HV),
      (∀ j, sobolevInjection (k : ℝ) (f j)=smulLeftCLM ℂ ξ (U j)) →
      ∃ q : H, sobolevInjection ((k : ℝ)-1) q=smulLeftCLM ℂ η (lowerPart z A V U i) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*‖f‖ := by
  obtain ⟨L₀,L₂,L₁,hL⟩ := exists_lower_realization k hη hcη hξ hcξ h1 A V i
  obtain ⟨C,hC,hn⟩ := quadratic_parameter_norm L₀ L₂ L₁
  refine ⟨C,hC,fun z U f hf => ⟨_,hL z U f hf,?_⟩⟩
  exact ((L₀+(∑ d, z d • L₁ d)+(∑ d, z d*z d) • L₂).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (hn z) (norm_nonneg f))

lemma normalized_laplacian (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (hn : n*m=1) (ho : o*(lam+m+m)=1) (U : Fin 4 → Dist) (i : Fin 4) :
    normPair z lam m n o (fun j => U j.succ) (U 0) i =
      Δ (U i)+lowerPart z (coeffA dc lam m n o) (coeffV dc lam m n o) U i := by
  rw [normalized_matrix z lam m n o hn ho,lapd_expand,lowerPart]
  abel

/-- One genuine interior regularity gain, with a phase-uniform polynomial bound.
There are no unproved local regularity assumptions: the input is actual Sobolev
representatives at the previous, possibly negative, integer order. -/
theorem scalar_principal_quantitative_gain (k : ℤ) {Ω : Set X} {χ η ξ : X → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hcξ : HasCompactSupport ξ)
    (h1 : Set.EqOn η 1 (tsupport χ)) (h2 : Set.EqOn ξ 1 (tsupport η))
    (hsη : tsupport η ⊆ Ω)
    (A : Fin 3 → Fin 4 → Fin 4 → Coeff) (V : Fin 4 → Fin 4 → Coeff) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (U F : Fin 4 → Dist) (f g : HV),
      (∀ i, LocalEq Ω (Δ (U i)+lowerPart z A V U i) (F i)) →
      (∀ i, sobolevInjection (k : ℝ) (f i)=smulLeftCLM ℂ ξ (U i)) →
      (∀ i, sobolevInjection ((k : ℝ)-1) (g i)=smulLeftCLM ℂ η (F i)) →
      ∃ q : HV, (∀ i, sobolevInjection ((k : ℝ)+1) (q i)=smulLeftCLM ℂ χ (U i)) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*(‖f‖+‖g‖) := by
  classical
  obtain ⟨M,hM⟩ := exists_bounded_integer_multiplier k hη hcη
  have hL (i : Fin 4) := lower_realization_bound k hη hcη hξ hcξ h2 A V i
  choose L hLp hL using hL
  obtain ⟨K,hK,hgain⟩ := quantitative_cutoff_gain k hχ hcχ hη hcη h1
  let C := K*(‖M‖+(∑ i, L i)+1)
  have hLs : 0 < ∑ i, L i := Finset.sum_pos (fun i _ => hLp i) Finset.univ_nonempty
  refine ⟨C,by dsimp [C]; positivity,fun z U F f g heq hf hg => ?_⟩
  have hZi : 0≤∑ d, ‖z d‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let W := (1+∑ d, ‖z d‖)^2
  have hW : 1 ≤ W := by dsimp [W]; nlinarith
  have hW0 : 0≤W := le_trans zero_le_one hW
  have hbase : ‖f‖+‖g‖ ≤ W*(‖f‖+‖g‖) := by nlinarith [norm_nonneg f,norm_nonneg g]
  have hcomp (i : Fin 4) : ∃ q : H,
      sobolevInjection ((k : ℝ)+1) q=smulLeftCLM ℂ χ (U i) ∧
      ‖q‖ ≤ C*W*(‖f‖+‖g‖) := by
    obtain ⟨r,hr,hrn⟩ := hL i z U f hf
    have hmid : sobolevInjection (k : ℝ) (M (f i))=smulLeftCLM ℂ η (U i) := by
      rw [hM,hf]
      exact nested_multiplier (hcη.hasTemperateGrowth hη) (hcξ.hasTemperateGrowth hξ) h2 _
    have hΔ : sobolevInjection ((k : ℝ)-1) (g i-r)=smulLeftCLM ℂ η (Δ (U i)) := by
      rw [map_sub,hg,hr]
      have hh := (heq i).cutoff hη hcη hsη
      rw [map_add] at hh
      exact (eq_sub_of_add_eq hh).symm
    obtain ⟨q,hq,hqn⟩ := hgain (U i) (M (f i)) (g i-r) hmid hΔ
    refine ⟨q,hq,hqn.trans ?_⟩
    have hnM : ‖M (f i)‖ ≤ ‖M‖*(W*(‖f‖+‖g‖)) := by
      apply (M.le_opNorm _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg M)
      exact (norm_le_pi_norm f i).trans ((le_add_of_nonneg_right (norm_nonneg g)).trans hbase)
    have hng : ‖g i‖ ≤ W*(‖f‖+‖g‖) :=
      (norm_le_pi_norm g i).trans ((le_add_of_nonneg_left (norm_nonneg f)).trans hbase)
    have hnr : ‖r‖ ≤ (∑ j, L j)*(W*(‖f‖+‖g‖)) := by
      apply hrn.trans
      change L i*W*‖f‖ ≤ (∑ j, L j)*(W*(‖f‖+‖g‖))
      have hLi : L i≤∑ j, L j := Finset.single_le_sum (fun j _ => (hLp j).le) (Finset.mem_univ i)
      calc
        _ ≤ (∑ j, L j)*W*(‖f‖+‖g‖) := by gcongr; exact le_add_of_nonneg_right (norm_nonneg g)
        _ = _ := by ring
    have hb : ‖M (f i)‖+‖g i-r‖ ≤ (‖M‖+(∑ j, L j)+1)*(W*(‖f‖+‖g‖)) := by
      have hh := norm_sub_le (g i) r
      nlinarith
    calc
      _ ≤ K*((‖M‖+(∑ j, L j)+1)*(W*(‖f‖+‖g‖))) := mul_le_mul_of_nonneg_left hb hK.le
      _ = _ := by dsimp [C]; ring
  choose q hq hqn using hcomp
  refine ⟨q,hq,?_⟩
  exact (pi_norm_le_iff_of_nonneg (by dsimp [C,W]; positivity)).mpr hqn

/-- The preceding estimate applies to the actual normalized physical system. -/
theorem normalized_quantitative_gain (k : ℤ) {Ω : Set X} {χ η ξ : X → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hcξ : HasCompactSupport ξ)
    (h1 : Set.EqOn η 1 (tsupport χ)) (h2 : Set.EqOn ξ 1 (tsupport η))
    (hsη : tsupport η ⊆ Ω) (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (U F : Fin 4 → Dist) (f g : HV),
      (∀ i, LocalEq Ω (normPair z lam m n o (fun j => U j.succ) (U 0) i) (F i)) →
      (∀ i, sobolevInjection (k : ℝ) (f i)=smulLeftCLM ℂ ξ (U i)) →
      (∀ i, sobolevInjection ((k : ℝ)-1) (g i)=smulLeftCLM ℂ η (F i)) →
      ∃ q : HV, (∀ i, sobolevInjection ((k : ℝ)+1) (q i)=smulLeftCLM ℂ χ (U i)) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*(‖f‖+‖g‖) := by
  obtain ⟨C,hC,hgain⟩ := scalar_principal_quantitative_gain k hχ hcχ hη hcη hξ hcξ h1 h2 hsη
    (coeffA dc lam m n o) (coeffV dc lam m n o)
  refine ⟨C,hC,fun z U F f g heq hf hg => hgain z U F f g (fun i => ?_) hf hg⟩
  simpa only [normalized_laplacian z lam m n o hn ho] using heq i
end
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
open ElasticityAugmented ElasticityRegularity
abbrev H3 := Fin 3 → ElasticityDistribution.H
lemma complex_zero_dist (u : Dist) : (0 : ℂ) • u=0 := zero_smul ℂ u
lemma complex_smul_dist_zero (c : ℂ) : c • (0 : Dist)=0 := @smul_zero ℂ Dist _ _ c

def lpProj (i : Fin 3) : H3 →L[ℂ] Dist :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure X) 2).comp (ContinuousLinearMap.proj i)
def divZeroCLM : H3 →L[ℂ] Dist :=
  ∑ i, (LineDeriv.lineDerivOpCLM ℂ Dist (e i)).comp (lpProj i)
lemma divZeroCLM_apply (f : H3) : divZeroCLM f=divd 0 (fun j => (f j : Dist)) := by
  simp only [divZeroCLM,sum_apply,ContinuousLinearMap.comp_apply,lpProj,
    ContinuousLinearMap.proj_apply,Lp.toTemperedDistributionCLM_apply,
    divd,sd_apply,Pi.zero_apply,complex_zero_dist,add_zero,dd_apply,LineDeriv.lineDerivOpCLM_apply]
lemma divd_affine (z : Fin 3 → ℂ) (U : Fin 3 → Dist) :
    divd z U=divd 0 U+∑ i, z i • U i := by
  simp only [divd,sd_apply,Pi.zero_apply,complex_zero_dist,add_zero,Finset.sum_add_distrib]

/-- A bounded Sobolev realization of an actual affine distribution family. All
mapping properties are proved in the concrete applications below. -/
theorem affine_cutoff_bound (s : ℝ) {η : X → ℂ}
    (T₀ : H3 →L[ℂ] Dist) (T₁ : Fin 3 → H3 →L[ℂ] Dist)
    (h₀ : ∀ f, MemSobolev s 2 (smulLeftCLM ℂ η (T₀ f)))
    (h₁ : ∀ d f, MemSobolev s 2 (smulLeftCLM ℂ η (T₁ d f))) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (f : H3),
      ∃ q : ElasticityDistribution.H,
        sobolevInjection s q=smulLeftCLM ℂ η (T₀ f+∑ d, z d • T₁ d f) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*‖f‖ := by
  obtain ⟨L₀,hL₀⟩ := exists_continuous_lift (sobolevInjection s) (sobolevInjection_injective s)
    ((smulLeftCLM ℂ η).comp T₀) (fun f => (memSobolev_iff_range s _).mp (h₀ f))
  have hL₁ (d : Fin 3) := exists_continuous_lift (sobolevInjection s) (sobolevInjection_injective s)
    ((smulLeftCLM ℂ η).comp (T₁ d)) (fun f => (memSobolev_iff_range s _).mp (h₁ d f))
  choose L₁ hL₁ using hL₁
  obtain ⟨C,hC,hb⟩ := quadratic_parameter_norm L₀ (0 : H3 →L[ℂ] ElasticityDistribution.H) L₁
  refine ⟨C,hC,fun z f => ⟨(L₀+∑ d, z d • L₁ d) f,?_,?_⟩⟩
  · simp only [add_apply,sum_apply,smul_apply,map_add,map_sum,map_smul,hL₀,hL₁,
      ContinuousLinearMap.comp_apply]
  · have hh := hb z
    simp only [smul_zero,add_zero] at hh
    exact ((L₀+∑ d, z d • L₁ d).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right hh (norm_nonneg f))

/-- Localized actual physical augmentation starts in H^-1 with polynomial phase
loss; its scalar component is the shifted divergence, not a new unknown. -/
theorem augmentation_cutoff_bound {η : X → ℂ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (f : H3),
      ∃ q : HV, (∀ i, sobolevInjection (-1) (q i)=smulLeftCLM ℂ η
        ((Fin.cons (divd z (fun j => (f j : Dist))) (fun j => (f j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*‖f‖ := by
  have hf (f : H3) (i : Fin 3) := lp_local_zero Set.univ (f i)
  obtain ⟨D,hD,hbD⟩ := affine_cutoff_bound (-1) divZeroCLM lpProj
    (fun f => by
      rw [divZeroCLM_apply]
      simpa only [zero_sub] using LocalSobolev.divergence (hf f) 0 η hη hcη (Set.subset_univ _))
    (fun i f => (hf f i η hη hcη (Set.subset_univ _)).mono (by norm_num))
  have hc (i : Fin 3) := affine_cutoff_bound (-1) (lpProj i) (fun _ => 0)
    (fun f => (hf f i η hη hcη (Set.subset_univ _)).mono (by norm_num))
    (fun _ _ => by simp only [zero_apply,map_zero]; exact memSobolev_fun_zero X ℂ _ _)
  choose B hB hb using hc
  let C := D+∑ i, B i
  have hs : 0≤∑ i, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨C,by dsimp [C]; positivity,fun z f => ?_⟩
  obtain ⟨q₀,hq₀,hn₀⟩ := hbD z f
  have hv (i : Fin 3) := hb i z f
  choose q hq hn using hv
  refine ⟨Fin.cons q₀ q,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Fin.cons_zero,divd_affine]
      simpa only [Fin.cons_zero,divZeroCLM_apply,lpProj,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply,Lp.toTemperedDistributionCLM_apply] using hq₀
    · simpa only [Fin.cons_succ,zero_apply,complex_smul_dist_zero,Finset.sum_const_zero,add_zero,lpProj,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
        Lp.toTemperedDistributionCLM_apply] using hq i
  · apply (pi_norm_le_iff_of_nonneg (by dsimp [C]; positivity)).mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · apply hn₀.trans
      gcongr
      exact le_add_of_nonneg_right hs
    · apply (hn i).trans
      gcongr
      have hh : B i≤∑ j, B j := Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)
      exact hh.trans (le_add_of_nonneg_left hD.le)

/-- The source of the actual normalized system is also H^-1, with a uniform
polynomial phase bound depending on the fixed coefficients and cutoff only. -/
theorem normSource_cutoff_bound {η : X → ℂ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) (m n o : Coeff) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (f : H3),
      ∃ q : HV, (∀ i, sobolevInjection (-1) (q i)=smulLeftCLM ℂ η
        (normSource z m n o (fun j => (f j : Dist)) i)) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*‖f‖ := by
  let T₀ : H3 →L[ℂ] Dist := (smulLeftCLM ℂ (eval o)).comp
    (divZeroCLM-(2 : ℂ) • (smulLeftCLM ℂ (eval n)).comp
      (∑ i, (smulLeftCLM ℂ (eval (dc i m))).comp (lpProj i)))
  let T₁ (i : Fin 3) : H3 →L[ℂ] Dist := (smulLeftCLM ℂ (eval o)).comp (lpProj i)
  have hT₀ (f : H3) : T₀ f=normSource 0 m n o (fun j => (f j : Dist)) 0 := by
    simp only [T₀,ContinuousLinearMap.comp_apply,sub_apply,smul_apply,sum_apply,
      divZeroCLM_apply,lpProj,ContinuousLinearMap.proj_apply,Lp.toTemperedDistributionCLM_apply,
      normSource,Fin.cons_zero,smul_def]
  have hT₁ (i : Fin 3) (f : H3) : T₁ i f=o • (f i : Dist) := rfl
  have hf (f : H3) (i : Fin 3) := lp_local_zero Set.univ (f i)
  obtain ⟨D,hD,hbD⟩ := affine_cutoff_bound (-1) T₀ T₁
    (fun f => by rw [hT₀]; simpa only [zero_sub] using normSource_local 0 m n o _ (hf f) 0 η hη hcη (Set.subset_univ _))
    (fun i f => ((LocalSobolev.coeff (hf f i) o) η hη hcη (Set.subset_univ _)).mono (by norm_num))
  have hc (i : Fin 3) := affine_cutoff_bound (-1)
    ((smulLeftCLM ℂ (eval n)).comp (lpProj i)) (fun _ => 0)
    (fun f => ((LocalSobolev.coeff (hf f i) n) η hη hcη (Set.subset_univ _)).mono (by norm_num))
    (fun _ _ => by simp only [zero_apply,map_zero]; exact memSobolev_fun_zero X ℂ _ _)
  choose B hB hb using hc
  let C := D+∑ i, B i
  have hs : 0≤∑ i, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨C,by dsimp [C]; positivity,fun z f => ?_⟩
  obtain ⟨q₀,hq₀,hn₀⟩ := hbD z f
  have hv (i : Fin 3) := hb i z f
  choose q hq hn using hv
  refine ⟨Fin.cons q₀ q,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Fin.cons_zero,hq₀,hT₀]
      congr 1
      simp only [normSource,Fin.cons_zero,hT₁]
      rw [divd_affine z]
      simp only [smul_def,map_sub,map_add,map_sum,map_smul]
      abel
    · simpa only [Fin.cons_succ,zero_apply,complex_smul_dist_zero,Finset.sum_const_zero,add_zero,lpProj,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
        Lp.toTemperedDistributionCLM_apply,normSource,smul_def] using hq i
  · apply (pi_norm_le_iff_of_nonneg (by dsimp [C]; positivity)).mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · apply hn₀.trans
      gcongr
      exact le_add_of_nonneg_right hs
    · apply (hn i).trans
      gcongr
      have hh : B i≤∑ j, B j := Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)
      exact hh.trans (le_add_of_nonneg_left hD.le)
end ElasticityDistribution
namespace ElasticityDistribution
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityAugmented ElasticityRegularity

lemma norm_pi_map_le (L : ElasticityDistribution.H →L[ℂ] ElasticityDistribution.H) (f : HV) :
    ‖fun i => L (f i)‖ ≤ ‖L‖*‖f‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg L) (norm_nonneg f))).mpr
  intro i
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm f i) (norm_nonneg L))

/-- Two interior gains for a genuine physical L2 solution, starting with its
actual H^-1 divergence, suffice for a polynomially bounded H^1 augmented
remainder. Arbitrarily high finite CGO expansions absorb this fixed loss. -/
theorem physical_quantitative_H1 {Ω : Set X} (χ : Fin 5 → X → ℂ)
    (hχ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i)) (hcχ : ∀ i, HasCompactSupport (χ i))
    (hnest : ∀ i : Fin 4, Set.EqOn (χ i.succ) 1 (tsupport (χ i.castSucc)))
    (hs : ∀ i, tsupport (χ i) ⊆ Ω)
    (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (r F : H3),
      (∀ i, LocalEq Ω (phys z lam m (fun j => (r j : Dist)) i) (F i : Dist)) →
      ∃ q : HV, (∀ i, sobolevInjection 1 (q i)=smulLeftCLM ℂ (χ 0)
        ((Fin.cons (divd z (fun j => (r j : Dist))) (fun j => (r j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^6*(‖r‖+‖F‖) := by
  obtain ⟨A,hA,haug⟩ := augmentation_cutoff_bound (hχ 4) (hcχ 4)
  obtain ⟨B,hB,hsrc₃⟩ := normSource_cutoff_bound (hχ 3) (hcχ 3) m n o
  obtain ⟨D,hD,hsrc₁⟩ := normSource_cutoff_bound (hχ 1) (hcχ 1) m n o
  obtain ⟨J,hJ⟩ := exists_bounded_sobolev_inclusion (E := X) (s := -1) (t := -2) (by norm_num)
  obtain ⟨K,hK,hgain₁⟩ := normalized_quantitative_gain (-1) (hχ 2) (hcχ 2)
    (hχ 3) (hcχ 3) (hχ 4) (hcχ 4) (hnest 2) (hnest 3) (hs 3) lam m n o hn ho
  obtain ⟨L,hL,hgain₂⟩ := normalized_quantitative_gain 0 (hχ 0) (hcχ 0)
    (hχ 1) (hcχ 1) (hχ 2) (hcχ 2) (hnest 0) (hnest 1) (hs 1) lam m n o hn ho
  let T := K*(A+‖J‖*B)
  let C := L*(T+D)
  have hT : 0<T := by dsimp [T]; positivity
  refine ⟨C,by dsimp [C]; positivity,fun z r F heq => ?_⟩
  let U : Fin 4 → Dist := Fin.cons (divd z (fun j => (r j : Dist))) (fun j => (r j : Dist))
  let FF := normSource z m n o (fun j => (F j : Dist))
  have hsys : ∀ i, LocalEq Ω (normPair z lam m n o (fun j => U j.succ) (U 0) i) (FF i) :=
    local_normalized_system z lam m n o _ _ heq
  obtain ⟨f,hf,hfn⟩ := haug z r
  obtain ⟨g₃,hg₃,hgn₃⟩ := hsrc₃ z F
  obtain ⟨g₁,hg₁,hgn₁⟩ := hsrc₁ z F
  have hg₂ (i : Fin 4) : sobolevInjection (-2) (J (g₃ i))=smulLeftCLM ℂ (χ 3) (FF i) := by
    rw [hJ,hg₃]
  have hf' (i : Fin 4) : sobolevInjection ((-1 : ℤ) : ℝ) (f i)=smulLeftCLM ℂ (χ 4) (U i) := by
    simpa only [Int.cast_neg,Int.cast_one] using hf i
  have hg₂' (i : Fin 4) : sobolevInjection (((-1 : ℤ) : ℝ)-1) (J (g₃ i))=
      smulLeftCLM ℂ (χ 3) (FF i) := by convert hg₂ i using 2; norm_num
  obtain ⟨v,hv,hvn⟩ := hgain₁ z U FF f (fun i => J (g₃ i)) hsys hf' hg₂'
  have hv' (i : Fin 4) : sobolevInjection ((0 : ℤ) : ℝ) (v i)=smulLeftCLM ℂ (χ 2) (U i) := by
    simpa only [Int.cast_neg,Int.cast_one,Int.cast_zero,neg_add_cancel] using hv i
  have hg₁' (i : Fin 4) : sobolevInjection (((0 : ℤ) : ℝ)-1) (g₁ i)=
      smulLeftCLM ℂ (χ 1) (FF i) := by simpa only [Int.cast_zero,zero_sub] using hg₁ i
  obtain ⟨q,hq,hqn⟩ := hgain₂ z U FF v g₁ hsys hv' hg₁'
  refine ⟨q,fun i => by simpa only [Int.cast_zero,zero_add] using hq i,?_⟩
  let W := (1+∑ d, ‖z d‖)^2
  let R := ‖r‖+‖F‖
  have hW : 1≤W := by
    have hh : 0≤∑ d, ‖z d‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp [W]; nlinarith
  have hW0 : 0≤W := zero_le_one.trans hW
  have hR : 0≤R := add_nonneg (norm_nonneg r) (norm_nonneg F)
  have hrR : ‖r‖≤R := le_add_of_nonneg_right (norm_nonneg F)
  have hFR : ‖F‖≤R := le_add_of_nonneg_left (norm_nonneg r)
  have hjn : ‖fun i => J (g₃ i)‖ ≤ ‖J‖*(B*W*‖F‖) :=
    (norm_pi_map_le J g₃).trans (mul_le_mul_of_nonneg_left hgn₃ (norm_nonneg J))
  have hvn' : ‖v‖≤T*W^2*R := by
    apply hvn.trans
    change K*W*(‖f‖+‖fun i => J (g₃ i)‖)≤T*W^2*R
    calc
      _ ≤ K*W*(A*W*‖r‖+‖J‖*(B*W*‖F‖)) := by gcongr
      _ ≤ K*W*(A*W*R+‖J‖*(B*W*R)) := by gcongr
      _ = _ := by dsimp [T]; ring
  have hgn₁' : ‖g₁‖≤D*W^2*R := by
    apply hgn₁.trans
    change D*W*‖F‖≤D*W^2*R
    have hWW : W≤W^2 := by nlinarith
    gcongr
  calc
    _ ≤ L*W*(‖v‖+‖g₁‖) := hqn
    _ ≤ L*W*(T*W^2*R+D*W^2*R) := by gcongr
    _ = C*(1+∑ d, ‖z d‖)^6*(‖r‖+‖F‖) := by dsimp [C,W,R]; ring
end ElasticityDistribution
namespace ElasticityDistribution
open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds

section
open ElasticityPhysicalAlgebra (phase)

lemma norm_ofLp_le (u : ElasticityPhysicalDual.H) : ‖(fun i => u i : H3)‖ ≤ ‖u‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr (fun i => PiLp.norm_apply_le u i)

lemma phase_envelope (α β : X) {h : ℝ} (hh : 0<h) (h1 : h≤1) :
    1+∑ i, ‖phase h α β i‖ ≤ h⁻¹*(1+∑ i, ‖(α i : ℂ)+Complex.I*(β i : ℂ)‖) := by
  have hi : 1≤h⁻¹ := (one_le_inv₀ hh).mpr h1
  simp only [phase]
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  nlinarith

/-- Actual physical correction with a proved polynomial interior bound. This
uses the uniform physical inverse and two true interior elliptic gains; taking
more terms in the finite CGO expansion absorbs its fixed sixth-power loss. -/
theorem physical_quantitative_correction (R : ℝ) (hR : 1≤R)
    (Ω : Set X) (hΩ : Ω ⊆ Metric.closedBall 0 R) (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x, star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x, star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0)
    (χ : Fin 5 → X → ℂ) (hχ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i))
    (hcχ : ∀ i, HasCompactSupport (χ i))
    (hnest : ∀ i : Fin 4, Set.EqOn (χ i.succ) 1 (tsupport (χ i.castSucc)))
    (hs : ∀ i, tsupport (χ i) ⊆ Ω) :
    ∃ C h₀ : ℝ, 0<C ∧ 0<h₀ ∧ ∀ h : ℝ, 0<h → h≤h₀ →
      ∀ f : Fin 3 → S, ∃ w : ElasticityPhysicalDual.H, ∃ q : HV,
        (∀ i, LocalEq Ω (phys (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
          (fun j => (w j : Dist)) i) (f i : Dist)) ∧
        (∀ i, sobolevInjection 1 (q i)=smulLeftCLM ℂ (χ 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖ ≤ C*‖ElasticityPhysicalDual.embed f‖ ∧
        ‖q‖ ≤ C*h⁻¹^6*‖ElasticityPhysicalDual.embed f‖ := by
  obtain ⟨A,h₀,hA,hh₀,hsol⟩ := weak_smooth_solvability R hR Ω hΩ α β hα lam m hl hm hrl hrm hm0 he0
  let n := inverseCoeff m hm hm0
  let o := inverseCoeff (lam+m+m) ((hl.add hm).add hm) he0
  have hn : n*exteriorCoeff m hm=1 := inverseCoeff_mul m hm hm0
  have ho : o*(exteriorCoeff lam hl+exteriorCoeff m hm+exteriorCoeff m hm)=1 := by
    apply Subtype.ext
    exact reciprocal_mul (lam+m+m) he0
  obtain ⟨B,hB,hest⟩ := physical_quantitative_H1 χ hχ hcχ hnest hs
    (exteriorCoeff lam hl) (exteriorCoeff m hm) n o hn ho
  let K := 1+∑ i, ‖(α i : ℂ)+Complex.I*(β i : ℂ)‖
  let C := A+B*K^6*(A+1)
  have hK : 0<K := by dsimp [K]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,min h₀ 1,hC,lt_min hh₀ zero_lt_one,fun h hh hsmall f => ?_⟩
  obtain ⟨w,hw,heq,_⟩ := hsol h hh (hsmall.trans (min_le_left _ _)) f
  let ff : H3 := fun i => ElasticityBessel.L2 (f i)
  have hfeq (i : Fin 3) : (ff i : Dist)=(f i : Dist) := by
    simp only [ff,ElasticityBessel.L2,SchwartzMap.toLpCLM_apply,Lp.toTemperedDistribution_toLp_eq]
  have heq' : ∀ i, LocalEq Ω (phys (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
      (fun j => (w j : Dist)) i) (ff i : Dist) := by simpa only [hfeq] using heq
  obtain ⟨q,hq,hqn⟩ := hest (phase h α β) (fun i => w i) ff heq'
  have hf : ‖ff‖≤‖ElasticityPhysicalDual.embed f‖ := by
    exact norm_ofLp_le (ElasticityPhysicalDual.embed f)
  have hr : ‖(fun i => w i : H3)‖≤A*‖ElasticityPhysicalDual.embed f‖ :=
    (norm_ofLp_le w).trans hw
  have hph : 1+∑ i, ‖phase h α β i‖ ≤ h⁻¹*K := phase_envelope α β hh (hsmall.trans (min_le_right _ _))
  have hB' : B*K^6*(A+1)≤C := le_add_of_nonneg_left hA.le
  have hA' : A≤C := le_add_of_nonneg_right (by positivity)
  refine ⟨w,q,heq,hq,hw.trans (mul_le_mul_of_nonneg_right hA' (norm_nonneg _)),?_⟩
  calc
    ‖q‖ ≤ B*(1+∑ i, ‖phase h α β i‖)^6*(‖(fun i => w i : H3)‖+‖ff‖) := hqn
    _ ≤ B*(h⁻¹*K)^6*(A*‖ElasticityPhysicalDual.embed f‖+‖ElasticityPhysicalDual.embed f‖) := by gcongr
    _ = (B*K^6*(A+1))*h⁻¹^6*‖ElasticityPhysicalDual.embed f‖ := by ring
    _ ≤ C*h⁻¹^6*‖ElasticityPhysicalDual.embed f‖ := by gcongr
end
open ElasticityPhysicalAlgebra (phase physical)

/-- The quantitative correction and classical representative are the SAME
physical solution. In particular no smooth solvability estimate is postulated. -/
theorem classical_quantitative_correction (R : ℝ) (hR : 1≤R)
    (Ω Ω' : Set X) (hΩ : Ω ⊆ Metric.closedBall 0 R) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x, star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x, star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0)
    (χ : Fin 5 → X → ℂ) (hχ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i))
    (hcχ : ∀ i, HasCompactSupport (χ i))
    (hnest : ∀ i : Fin 4, Set.EqOn (χ i.succ) 1 (tsupport (χ i.castSucc)))
    (hs : ∀ i, tsupport (χ i) ⊆ Ω) (h1 : Set.EqOn (χ 0) 1 Ω') :
    ∃ C h₀ : ℝ, 0<C ∧ 0<h₀ ∧ ∀ h : ℝ, 0<h → h≤h₀ →
      ∀ f : Fin 3 → S, ∃ w : ElasticityPhysicalDual.H, ∃ q : HV, ∃ v : Fin 3 → S,
        (∀ i, ∀ᵐ x ∂(volume : Measure X), x ∈ Ω' → w i x=v i x) ∧
        (∀ i, Set.EqOn (physical (phase h α β) (eval (exteriorCoeff lam hl))
          (eval (exteriorCoeff m hm)) v i : X → ℂ) (f i : X → ℂ) Ω') ∧
        (∀ i, sobolevInjection 1 (q i)=smulLeftCLM ℂ (χ 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖ ≤ C*‖ElasticityPhysicalDual.embed f‖ ∧
        ‖q‖ ≤ C*h⁻¹^6*‖ElasticityPhysicalDual.embed f‖ := by
  obtain ⟨C,h₀,hC,hh₀,hsol⟩ := physical_quantitative_correction R hR Ω hΩ α β hα
    lam m hl hm hrl hrm hm0 he0 χ hχ hcχ hnest hs
  refine ⟨C,h₀,hC,hh₀,fun h hh hsmall f => ?_⟩
  obtain ⟨w,q,heq,hq,hw,hqn⟩ := hsol h hh hsmall f
  let n := inverseCoeff m hm hm0
  let o := inverseCoeff (lam+m+m) ((hl.add hm).add hm) he0
  have hn : n*exteriorCoeff m hm=1 := inverseCoeff_mul m hm hm0
  have ho : o*(exteriorCoeff lam hl+exteriorCoeff m hm+exteriorCoeff m hm)=1 := by
    apply Subtype.ext
    exact reciprocal_mul (lam+m+m) he0
  obtain ⟨v,hv,hphys⟩ := classical_representative hΩ' hsub (phase h α β)
    (exteriorCoeff lam hl) (exteriorCoeff m hm) n o hn ho w f heq (hχ 0) (hcχ 0) (hs 0) h1
  exact ⟨w,q,v,hv,hphys,hq,hw,hqn⟩
end ElasticityDistribution
namespace ElasticityDistribution
open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalDual (embed)

/-- The two true terms in the physical residual at truncation order eight. -/
def finiteResidual (h : ℝ) (f₀ f₁ : Fin 3 → S) : Fin 3 → S :=
  (h : ℂ)^8 • f₀+(h : ℂ)^7 • f₁

lemma finiteResidual_bound (h : ℝ) (hh : 0≤h) (h1 : h≤1) (f₀ f₁ : Fin 3 → S) :
    ‖embed (finiteResidual h f₀ f₁)‖ ≤ h^7*(‖embed f₀‖+‖embed f₁‖) := by
  have hp : h^8≤h^7 := by nlinarith [pow_nonneg hh 7]
  calc
    ‖embed (finiteResidual h f₀ f₁)‖ ≤ ‖(h : ℂ)^8 • embed f₀‖+‖(h : ℂ)^7 • embed f₁‖ := by
      simpa only [finiteResidual,map_add,map_smul] using
        norm_add_le ((h : ℂ)^8 • embed f₀) ((h : ℂ)^7 • embed f₁)
    _ = h^8*‖embed f₀‖+h^7*‖embed f₁‖ := by
      simp only [norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh]
    _ ≤ h^7*(‖embed f₀‖+‖embed f₁‖) := by nlinarith [norm_nonneg (embed f₀)]

/-- Finite physical CGO residuals have a classical correction whose full
physical-divergence H1 error tends to zero at an explicit linear rate. -/
theorem finite_classical_correction (R : ℝ) (hR : 1≤R)
    (Ω Ω' : Set X) (hΩ : Ω ⊆ Metric.closedBall 0 R) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x, star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x, star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0)
    (χ : Fin 5 → X → ℂ) (hχ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i))
    (hcχ : ∀ i, HasCompactSupport (χ i))
    (hnest : ∀ i : Fin 4, Set.EqOn (χ i.succ) 1 (tsupport (χ i.castSucc)))
    (hs : ∀ i, tsupport (χ i) ⊆ Ω) (h1 : Set.EqOn (χ 0) 1 Ω')
    (f₀ f₁ : Fin 3 → S) :
    ∃ C h₀ : ℝ, 0<C ∧ 0<h₀ ∧ ∀ h : ℝ, 0<h → h≤h₀ →
      ∃ w : ElasticityPhysicalDual.H, ∃ q : HV, ∃ v : Fin 3 → S,
        (∀ i, ∀ᵐ x ∂(volume : Measure X), x ∈ Ω' → w i x=v i x) ∧
        (∀ i, Set.EqOn (physical (phase h α β) (eval (exteriorCoeff lam hl))
          (eval (exteriorCoeff m hm)) v i : X → ℂ) (finiteResidual h f₀ f₁ i : X → ℂ) Ω') ∧
        (∀ i, sobolevInjection 1 (q i)=smulLeftCLM ℂ (χ 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖ ≤ C*h^7 ∧ ‖q‖ ≤ C*h := by
  obtain ⟨A,h₀,hA,hh₀,hsol⟩ := classical_quantitative_correction R hR Ω Ω' hΩ hΩ' hsub
    α β hα lam m hl hm hrl hrm hm0 he0 χ hχ hcχ hnest hs h1
  let K := ‖embed f₀‖+‖embed f₁‖
  let C := A*(K+1)
  have hK : 0≤K := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hC : 0<C := mul_pos hA (by linarith)
  refine ⟨C,min h₀ 1,hC,lt_min hh₀ zero_lt_one,fun h hh hsmall => ?_⟩
  obtain ⟨w,q,v,hv,hphys,hq,hw,hqn⟩ := hsol h hh (hsmall.trans (min_le_left _ _))
    (finiteResidual h f₀ f₁)
  have hf := finiteResidual_bound h hh.le (hsmall.trans (min_le_right _ _)) f₀ f₁
  have hAK : A*K≤C := by dsimp [C]; nlinarith
  refine ⟨w,q,v,hv,hphys,hq,?_,?_⟩
  · calc
      ‖w‖ ≤ A*(h^7*K) := hw.trans (mul_le_mul_of_nonneg_left hf hA.le)
      _ ≤ C*h^7 := by nlinarith [pow_nonneg hh.le 7]
  · calc
      ‖q‖ ≤ A*h⁻¹^6*(h^7*K) := hqn.trans (mul_le_mul_of_nonneg_left hf (by positivity))
      _ = (A*K)*h := by field_simp
      _ ≤ C*h := mul_le_mul_of_nonneg_right hAK hh.le

lemma correction_cancels_residual (Ω : Set X) (z : Fin 3 → ℂ) (lam m : X → ℂ)
    (u v f : Fin 3 → S)
    (hu : ∀ i, Set.EqOn (physical z lam m u i : X → ℂ) (f i : X → ℂ) Ω)
    (hv : ∀ i, Set.EqOn (physical z lam m v i : X → ℂ) (f i : X → ℂ) Ω) :
    ∀ i, Set.EqOn (physical z lam m (u-v) i : X → ℂ) 0 Ω := by
  have he := (ElasticityPhysicalDual.physicalLM z lam m).map_sub u v
  change physical z lam m (u-v)=physical z lam m u-physical z lam m v at he
  intro i x hx
  rw [he]
  change physical z lam m u i x-physical z lam m v i x=0
  rw [hu i hx,hv i hx,sub_self]
end ElasticityDistribution

end

end OAI
