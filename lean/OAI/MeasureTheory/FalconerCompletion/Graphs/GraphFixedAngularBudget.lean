import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphDescendants

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

lemma graph_fixed_angular_budget {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {ψ : V → ℂ} (hψ : ContDiff ℝ ∞ ψ) (m : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j ψ w‖ ≤ P := by
  have hb (j : ℕ) := (isCompact_sphere (0:V) 1).exists_bound_of_continuousOn
    (hψ.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))).continuousOn
  choose C hC using hb
  refine ⟨∑ j ∈ Finset.range (m+1), max 0 (C j),Finset.sum_nonneg (fun _ _ => le_max_left _ _),?_⟩
  intro j hj w hw
  exact ((hC j w (by simpa only [Metric.mem_sphere,dist_zero_right] using hw)).trans
    (le_max_right _ _)).trans (Finset.single_le_sum (fun _ _ => le_max_left _ _)
      (Finset.mem_range.mpr (by omega)))

lemma graph_cap_with_angular_jet (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ A : ℝ) (k : Fin d → ℤ) (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
      (P : ℝ), 0 < δ → δ⁻¹ ≤ A → 1 ≤ A → 0 ≤ P → ContDiff ℝ ∞ ψ →
      (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j ψ w‖ ≤ P) →
    ∀ j ≤ m, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (fun w => (tensorCapND δ k w:ℂ)*ψ w) w‖ ≤ (C*P*2^m)*A^j := by
  obtain ⟨C,hC,hb⟩ := graphCapJet d m
  refine ⟨C,hC,?_⟩
  intro δ A k ψ P hδ hδA hA hP hψ hdψ j hj w hw
  exact graphJetMul (Complex.ofRealCLM.contDiff.comp (tensorCapND_contDiff δ k)) hψ m
    hC hP (le_trans (by norm_num) hA) w (fun j hj => hb δ A k hδ hδA w j hj)
    (fun j hj => (hdψ j hj w hw).trans
      (le_mul_of_one_le_right hP (one_le_pow₀ hA))) j hj

end CurrentFalconer
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace ContDiff

theorem graph_cap_four_decay (d : ℕ) {sig c₀ G : ℝ}
    (hsig : 0 < sig) (hc₀ : 0 < c₀) (hG : 0 ≤ G) (T : ℝ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (a p v L : ℝ), p-a ≤ v-p+2*sig*N → L ≤ v-p+2*sig*N → 0 ≤ v-p →
    let R := (2:ℝ)^N
    let δ := min c₀ (((2:ℝ)^(p-a))⁻¹*R^(10*sig))
    let τ := (2:ℝ)^(-p)*R^(30*sig)
    let S := R^sig*max 1 ((2:ℝ)^L*R^(-50*sig))
    ∀ (μ₁ μ₂ μ₃ μ₄ : Measure (EuclideanSpace ℝ (Fin d))),
    ∀ [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄],
    ∀ (Ψ : ℝ → ℂ) (K B P : ℝ) (k₁ k₂ : Fin d → ℤ)
      (u₁ u₂ : EuclideanSpace ℝ (Fin d))
      (ψ₁ ψ₂ : EuclideanSpace ℝ (Fin d) → ℂ)
      (b₁ b₂ b₃ b₄ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ),
    k₁ ∈ sphereCapGridND d δ → k₂ ∈ sphereCapGridND d δ →
    ContDiff ℝ ∞ Ψ → tsupport Ψ ⊆ Icc (1/4:ℝ) 4 →
    (∫ u : ℝ, ‖Ψ u‖) ≤ K → (∀ u, ‖iteratedDeriv m Ψ u‖ ≤ K) → 0 ≤ K → 0 ≤ P →
    ContDiff ℝ ∞ ψ₁ → ContDiff ℝ ∞ ψ₂ →
    (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j ψ₁ w‖ ≤ P) →
    (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j ψ₂ w‖ ≤ P) →
    GraphSymbolJet b₁ m S B → GraphSymbolJet b₂ m S B →
    GraphSymbolJet b₃ m S B → GraphSymbolJet b₄ m S B →
    (∀ᵐ z ∂(μ₁.prod μ₂).prod (μ₃.prod μ₄),
      ‖z.1.1-z.1.2‖ ≤ G*(2:ℝ)^(-a) ∧ ‖z.2.1-z.2.2‖ ≤ G*(2:ℝ)^(-a) ∧
      ‖(z.1.1-z.1.2)-u₁‖ ≤ G*(2:ℝ)^(-p) ∧ ‖(z.2.1-z.2.2)-u₂‖ ≤ G*(2:ℝ)^(-p)) →
    ¬(‖u₁-inner ℝ u₁ (sphereCapCenterND δ k₁) • sphereCapCenterND δ k₁‖ ≤ τ ∧
      ‖u₂-inner ℝ u₂ (sphereCapCenterND δ k₂) • sphereCapCenterND δ k₂‖ ≤ τ ∧
      |inner ℝ (sphereCapCenterND δ k₁) u₁+inner ℝ (sphereCapCenterND δ k₂) u₂| ≤ τ) →
    ‖∫ q : ℝ×((EuclideanSpace ℝ (Fin d))×(EuclideanSpace ℝ (Fin d))), Ψ (q.1/(2:ℝ)^v)*
      ((tensorCapND δ k₁ q.2.1:ℂ)*ψ₁ q.2.1 * sourceAngularTransformND μ₁ univ 1 b₁ q.1 q.2.1 *
        conj (sourceAngularTransformND μ₂ univ 1 b₂ q.1 q.2.1))*
      ((tensorCapND δ k₂ q.2.2:ℂ)*ψ₂ q.2.2 * sourceAngularTransformND μ₃ univ 1 b₃ q.1 q.2.2 *
        conj (sourceAngularTransformND μ₄ univ 1 b₄ q.1 q.2.2))
      ∂volume.prod ((canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))).prod
        (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))))‖ ≤
      C*K*P^2*B^4*R^(-T)*(2:ℝ)^v*((μ₁.prod μ₂).prod (μ₃.prod μ₄)).real univ := by
  obtain ⟨m,C,hC,N₀,hraw⟩ := graph_source_raw_four_decay
    (V:=EuclideanSpace ℝ (Fin d)) hsig hc₀ (by positivity : (0:ℝ) ≤ 2*(d+1:ℝ)) hG T
  obtain ⟨D,hD,hcap⟩ := graph_cap_with_angular_jet d m
  refine ⟨m,C*D^2*((2:ℝ)^m)^6,by positivity,N₀,?_⟩
  intro N hN a p v L hh hL hv R δ τ S μ₁ μ₂ μ₃ μ₄ _ _ _ _ Ψ K B P k₁ k₂ u₁ u₂
    ψ₁ ψ₂ b₁ b₂ b₃ b₄ hk₁ hk₂ hΨ hsΨ hK hdΨ hK0 hP hψ₁ hψ₂ hdψ₁ hdψ₂
    hb₁ hb₂ hb₃ hb₄ hgeo hne
  have hδ : 0 < δ := lt_min hc₀ (by positivity)
  have hS : 0 ≤ S := by positivity
  have hB := hb₁.nonneg
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  let A := 1+S+δ⁻¹
  have hSA : S ≤ A := by dsimp [A]; linarith
  have hδA : δ⁻¹ ≤ A := by dsimp [A]; linarith
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  let θ₁ := fun w => (tensorCapND δ k₁ w:ℂ)*ψ₁ w
  let θ₂ := fun w => (tensorCapND δ k₂ w:ℂ)*ψ₂ w
  have hθ₁ : ContDiff ℝ ∞ θ₁ := (Complex.ofRealCLM.contDiff.comp (tensorCapND_contDiff δ k₁)).mul hψ₁
  have hθ₂ : ContDiff ℝ ∞ θ₂ := (Complex.ofRealCLM.contDiff.comp (tensorCapND_contDiff δ k₂)).mul hψ₂
  have hdθ₁ := hcap δ A k₁ ψ₁ P hδ hδA hA1 hP hψ₁ hdψ₁
  have hdθ₂ := hcap δ A k₂ ψ₂ P hδ hδA hA1 hP hψ₂ hdψ₂
  have hpair₁ := graph_symbol_pair_budget hb₁ hb₂ hθ₁ hS hSA (by positivity : 0 ≤ D*P*2^m) hdθ₁
  have hpair₂ := graph_symbol_pair_budget hb₃ hb₄ hθ₂ hS hSA (by positivity : 0 ≤ D*P*2^m) hdθ₂
  have hPθ : 0 ≤ D*P*2^m := by positivity
  have hnθ₁ (w) (hw : ‖w‖=1) : ‖θ₁ w‖ ≤ D*P*2^m := by
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hdθ₁ 0 (Nat.zero_le _) w hw
  have hnθ₂ (w) (hw : ‖w‖=1) : ‖θ₂ w‖ ≤ D*P*2^m := by
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hdθ₂ 0 (Nat.zero_le _) w hw
  have hs₁ (w) (hw : ‖w‖=1) (hne : θ₁ w ≠ 0) :
      ‖w-sphereCapCenterND δ k₁‖ ≤ 2*(d+1:ℝ)*δ := by
    have hn : tensorCapND δ k₁ w ≠ 0 := by intro h; simp [θ₁,h] at hne
    exact sphereCapCenterND_dist hδ hk₁ hw (subset_closure hn)
  have hs₂ (w) (hw : ‖w‖=1) (hne : θ₂ w ≠ 0) :
      ‖w-sphereCapCenterND δ k₂‖ ≤ 2*(d+1:ℝ)*δ := by
    have hn : tensorCapND δ k₂ w ≠ 0 := by intro h; simp [θ₂,h] at hne
    exact sphereCapCenterND_dist hδ hk₂ hw (subset_closure hn)
  have h := hraw N hN a p v L hh hL hv μ₁ μ₂ μ₃ μ₄ Ψ
    (sphereCapCenterND δ k₁) (sphereCapCenterND δ k₂) u₁ u₂ K
    (D*P*2^m*B*2^m*B*2^m) (D*P*2^m*B*2^m*B*2^m)
    θ₁ θ₂ b₁ b₂ b₃ b₄ (D*P*2^m) (D*P*2^m) B B B B
    hΨ hsΨ hK hdΨ (sphereCapCenterND_norm hk₁) (sphereCapCenterND_norm hk₂)
    hK0 (by positivity) (by positivity) hθ₁.continuous.measurable hθ₂.continuous.measurable
    hb₁.measurable hb₂.measurable hb₃.measurable hb₄.measurable
    hPθ hPθ hb₁.nonneg hb₂.nonneg hb₃.nonneg hb₄.nonneg hnθ₁ hnθ₂
    hb₁.norm_le hb₂.norm_le hb₃.norm_le hb₄.norm_le hgeo hne
    hpair₁.1 hpair₂.1 hpair₁.2 hpair₂.2 hs₁ hs₂
  exact h.trans_eq (by ring)

end CurrentFalconer
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set MeasureTheory
open scoped ComplexConjugate
variable {V : Type*} [MeasurableSpace V]

lemma graph_four_zero_of_ineligible (σ : Measure V) [SFinite σ]
    (Ψ : ℝ → ℂ) (η₁ η₂ : V → ℝ) (ψ₁ ψ₂ : V → ℂ)
    (U₁ U₂ U₃ U₄ : ℝ×V → ℂ)
    (hz : (∀ᵐ w ∂σ, η₁ w=0 ∨ ∀ r, U₁ (r,w)=0) ∨
      (∀ᵐ w ∂σ, η₁ w=0 ∨ ∀ r, U₂ (r,w)=0) ∨
      (∀ᵐ w ∂σ, η₂ w=0 ∨ ∀ r, U₃ (r,w)=0) ∨
      (∀ᵐ w ∂σ, η₂ w=0 ∨ ∀ r, U₄ (r,w)=0)) :
    (∫ q : ℝ×(V×V), Ψ q.1*
      ((η₁ q.2.1:ℂ)*ψ₁ q.2.1*U₁ (q.1,q.2.1)*conj (U₂ (q.1,q.2.1)))*
      ((η₂ q.2.2:ℂ)*ψ₂ q.2.2*U₃ (q.1,q.2.2)*conj (U₄ (q.1,q.2.2)))
      ∂volume.prod (σ.prod σ))=0 := by
  apply integral_eq_zero_of_ae
  rcases hz with hz | hz | hz | hz
  · have h : ∀ᵐ z : V×V ∂σ.prod σ, η₁ z.1=0 ∨ ∀ r, U₁ (r,z.1)=0 :=
      Measure.quasiMeasurePreserving_fst.ae hz
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae h] with q hq
    rcases hq with hq | hq <;> simp [hq]
  · have h : ∀ᵐ z : V×V ∂σ.prod σ, η₁ z.1=0 ∨ ∀ r, U₂ (r,z.1)=0 :=
      Measure.quasiMeasurePreserving_fst.ae hz
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae h] with q hq
    rcases hq with hq | hq <;> simp [hq]
  · have h : ∀ᵐ z : V×V ∂σ.prod σ, η₂ z.2=0 ∨ ∀ r, U₃ (r,z.2)=0 :=
      Measure.quasiMeasurePreserving_snd.ae hz
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae h] with q hq
    rcases hq with hq | hq <;> simp [hq]
  · have h : ∀ᵐ z : V×V ∂σ.prod σ, η₂ z.2=0 ∨ ∀ r, U₄ (r,z.2)=0 :=
      Measure.quasiMeasurePreserving_snd.ae hz
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae h] with q hq
    rcases hq with hq | hq <;> simp [hq]

end CurrentFalconer
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace
variable {d : ℕ}

lemma graph_cell_cap_ineligible (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
    {a p : ℕ} {X P : CellPath d} (hP : P ∈ graphChildren ρ a p X)
    (M δ : ℝ) (k : Fin d → ℤ) {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ}
    {m : ℕ} {s B : ℝ} (hb : GraphSymbolJet b m s B)
    (hn : P ∉ eligibleCells ρ a p X (tensorCapND δ k) b) :
    ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)), tensorCapND δ k w=0 ∨
      ∀ r, sourceAngularTransformND ρ (treeCell P) M b r w=0 := by
  apply graph_uneligible_transform ρ _ (treeCell P) M (tensorCapND δ k) b
    (tensorCapND_contDiff δ k).continuous.measurable hb.measurable (by norm_num : (0:ℝ) ≤ 1)
    hb.nonneg (Filter.Eventually.of_forall (tensorCapND_nonneg δ k))
    (Filter.Eventually.of_forall (tensorCapND_le_one δ k))
    (canonicalSphereMeasureND_ae_norm.mono (fun w hw x => hb.norm_le x w hw))
  exact fun h => hn ((graphChildren_eligible_iff hP).mpr h)

lemma graph_children_transform_split (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
    {a p : ℕ} (hap : a ≤ p) {X : CellPath d} (hX : X ∈ dyadicPaths a)
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ}
    {m : ℕ} {s B : ℝ} (hb : GraphSymbolJet b m s B)
    {Ma Mp : ℝ} (hMp : Mp ≠ 0) (r : ℝ) (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖=1) :
    sourceAngularTransformND ρ (treeCell X) Ma b r w =
      (Mp/Ma) • ∑ P ∈ graphChildren ρ a p X, sourceAngularTransformND ρ (treeCell P) Mp b r w := by
  have hm : Measurable (fun x => spherePlaneWaveND r x w*b x w) :=
    (show Measurable (fun x => spherePlaneWaveND r x w) by unfold spherePlaneWaveND; fun_prop).mul
      (hb.measurable.comp (measurable_id.prodMk measurable_const))
  have hi : IntegrableOn (fun x => spherePlaneWaveND r x w*b x w) (treeCell X) ρ := by
    apply Integrable.of_bound hm.aestronglyMeasurable B
    filter_upwards with x
    simpa only [norm_mul,spherePlaneWaveND_norm,one_mul] using hb.norm_le x w hw
  simp only [sourceAngularTransformND]
  rw [graphChildren_integral ρ hap hX _ hi, ←Finset.smul_sum, smul_smul]
  congr 1
  field_simp

end CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {d : ℕ}

noncomputable def graphDirectCellTerm
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) (M₁ M₂ : ℝ)
    (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
    (Ψ : ℝ → ℝ) (v δ : ℝ) (k₁ k₂ : Fin d → ℤ)
    (row col : CellPath d × CellPath d) : ℂ :=
  ∫ q : ℝ×((EuclideanSpace ℝ (Fin d))×(EuclideanSpace ℝ (Fin d))),
    (Ψ (q.1/(2:ℝ)^v):ℂ)*((tensorCapND δ k₁ q.2.1*tensorCapND δ k₂ q.2.2):ℂ)*
      ((sourceAngularTransformND ρ (treeCell row.1) M₁ b q.1 q.2.1 *
        sourceAngularTransformND κ (treeCell row.2) M₂ c q.1 q.2.2)*
       conj (sourceAngularTransformND ρ (treeCell col.1) M₁ b q.1 q.2.1 *
        sourceAngularTransformND κ (treeCell col.2) M₂ c q.1 q.2.2))
  ∂volume.prod ((canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))).prod
    (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))))

noncomputable def graphCrossedCellTerm
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) (M₁ M₂ : ℝ)
    (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
    (Ψ : ℝ → ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℂ) (v δ : ℝ) (k₁ k₂ : Fin d → ℤ)
    (row col : CellPath d × CellPath d) : ℂ :=
  ∫ q : ℝ×((EuclideanSpace ℝ (Fin d))×(EuclideanSpace ℝ (Fin d))),
    (Ψ (q.1/(2:ℝ)^v):ℂ)*((tensorCapND δ k₁ q.2.1*tensorCapND δ k₂ q.2.2):ℂ)*
      (((ψ q.2.1*sourceAngularTransformND ρ (treeCell row.1) M₁ b q.1 q.2.1) *
        sourceAngularTransformND κ (treeCell row.2) M₂ c q.1 q.2.2)*
       conj ((ψ q.2.2*sourceAngularTransformND ρ (treeCell col.1) M₁ b q.1 q.2.2) *
        sourceAngularTransformND κ (treeCell col.2) M₂ c q.1 q.2.1))
  ∂volume.prod ((canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))).prod
    (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))))

lemma graphDirectCellTerm_eq (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) (M₁ M₂ : ℝ)
    (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
    (Ψ : ℝ → ℝ) (v δ : ℝ) (k₁ k₂ : Fin d → ℤ) (row col : CellPath d × CellPath d) :
    graphDirectCellTerm ρ κ M₁ M₂ b c Ψ v δ k₁ k₂ row col =
    ∫ q : ℝ×((EuclideanSpace ℝ (Fin d))×(EuclideanSpace ℝ (Fin d))), (Ψ (q.1/(2:ℝ)^v):ℂ)*
      ((tensorCapND δ k₁ q.2.1:ℂ)*1*sourceAngularTransformND ρ (treeCell row.1) M₁ b q.1 q.2.1 *
        conj (sourceAngularTransformND ρ (treeCell col.1) M₁ b q.1 q.2.1))*
      ((tensorCapND δ k₂ q.2.2:ℂ)*1*sourceAngularTransformND κ (treeCell row.2) M₂ c q.1 q.2.2 *
        conj (sourceAngularTransformND κ (treeCell col.2) M₂ c q.1 q.2.2))
      ∂volume.prod ((canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))).prod
        (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)))) := by
  apply integral_congr_ae
  filter_upwards with q
  simp only [map_mul]
  ring

lemma graphCrossedCellTerm_eq (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) (M₁ M₂ : ℝ)
    (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
    (Ψ : ℝ → ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (v δ : ℝ) (k₁ k₂ : Fin d → ℤ) (row col : CellPath d × CellPath d) :
    graphCrossedCellTerm ρ κ M₁ M₂ b c Ψ ψ v δ k₁ k₂ row col =
    ∫ q : ℝ×((EuclideanSpace ℝ (Fin d))×(EuclideanSpace ℝ (Fin d))), (Ψ (q.1/(2:ℝ)^v):ℂ)*
      ((tensorCapND δ k₁ q.2.1:ℂ)*ψ q.2.1*sourceAngularTransformND ρ (treeCell row.1) M₁ b q.1 q.2.1 *
        conj (sourceAngularTransformND κ (treeCell col.2) M₂ c q.1 q.2.1))*
      ((tensorCapND δ k₂ q.2.2:ℂ)*conj (ψ q.2.2)*sourceAngularTransformND κ (treeCell row.2) M₂ c q.1 q.2.2 *
        conj (sourceAngularTransformND ρ (treeCell col.1) M₁ b q.1 q.2.2))
      ∂volume.prod ((canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))).prod
        (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)))) := by
  apply integral_congr_ae
  filter_upwards with q
  simp only [map_mul]
  ring

lemma graph_direct_ineligible_zero
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    {a p : ℕ} {X Y : CellPath d} {row col : CellPath d × CellPath d}
    (hr : row ∈ (graphChildren ρ a p X).product (graphChildren κ a p Y))
    (hc : col ∈ (graphChildren ρ a p X).product (graphChildren κ a p Y))
    (M₁ M₂ : ℝ) {b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ}
    {m : ℕ} {s B : ℝ} (hb : GraphSymbolJet b m s B) (hcj : GraphSymbolJet c m s B)
    (Ψ : ℝ → ℝ) (v δ : ℝ) (k₁ k₂ : Fin d → ℤ)
    (hin : ¬(row ∈ (eligibleCells ρ a p X (tensorCapND δ k₁) b).product
       (eligibleCells κ a p Y (tensorCapND δ k₂) c) ∧
      col ∈ (eligibleCells ρ a p X (tensorCapND δ k₁) b).product
       (eligibleCells κ a p Y (tensorCapND δ k₂) c))) :
    graphDirectCellTerm ρ κ M₁ M₂ b c Ψ v δ k₁ k₂ row col = 0 := by
  rw [graphDirectCellTerm_eq]
  apply graph_four_zero_of_ineligible (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)))
    (fun r => (Ψ (r/(2:ℝ)^v):ℂ)) (tensorCapND δ k₁) (tensorCapND δ k₂)
    (fun _ => 1) (fun _ => 1)
    (fun q => sourceAngularTransformND ρ (treeCell row.1) M₁ b q.1 q.2)
    (fun q => sourceAngularTransformND ρ (treeCell col.1) M₁ b q.1 q.2)
    (fun q => sourceAngularTransformND κ (treeCell row.2) M₂ c q.1 q.2)
    (fun q => sourceAngularTransformND κ (treeCell col.2) M₂ c q.1 q.2)
  have hr := Finset.mem_product.mp hr
  have hc := Finset.mem_product.mp hc
  by_cases h₁ : row.1 ∈ eligibleCells ρ a p X (tensorCapND δ k₁) b
  · by_cases h₂ : col.1 ∈ eligibleCells ρ a p X (tensorCapND δ k₁) b
    · by_cases h₃ : row.2 ∈ eligibleCells κ a p Y (tensorCapND δ k₂) c
      · exact Or.inr (Or.inr (Or.inr (graph_cell_cap_ineligible κ hc.2 M₂ δ k₂ hcj
          (fun h₄ => hin ⟨Finset.mem_product.mpr ⟨h₁,h₃⟩,Finset.mem_product.mpr ⟨h₂,h₄⟩⟩))))
      · exact Or.inr (Or.inr (Or.inl (graph_cell_cap_ineligible κ hr.2 M₂ δ k₂ hcj h₃)))
    · exact Or.inr (Or.inl (graph_cell_cap_ineligible ρ hc.1 M₁ δ k₁ hb h₂))
  · exact Or.inl (graph_cell_cap_ineligible ρ hr.1 M₁ δ k₁ hb h₁)

lemma graph_crossed_ineligible_zero
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    {a p : ℕ} {X Y : CellPath d} {row col : CellPath d × CellPath d}
    (hr : row ∈ (graphChildren ρ a p X).product (graphChildren κ a p Y))
    (hc : col ∈ (graphChildren ρ a p X).product (graphChildren κ a p Y))
    (M₁ M₂ : ℝ) {b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ}
    {m : ℕ} {s B : ℝ} (hb : GraphSymbolJet b m s B) (hcj : GraphSymbolJet c m s B)
    (Ψ : ℝ → ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℂ) (v δ : ℝ) (k₁ k₂ : Fin d → ℤ)
    (hin : ¬(row ∈ (eligibleCells ρ a p X (tensorCapND δ k₁) b).product
       (eligibleCells κ a p Y (tensorCapND δ k₂) c) ∧
      col ∈ (eligibleCells ρ a p X (tensorCapND δ k₂) b).product
       (eligibleCells κ a p Y (tensorCapND δ k₁) c))) :
    graphCrossedCellTerm ρ κ M₁ M₂ b c Ψ ψ v δ k₁ k₂ row col = 0 := by
  rw [graphCrossedCellTerm_eq]
  apply graph_four_zero_of_ineligible (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)))
    (fun r => (Ψ (r/(2:ℝ)^v):ℂ)) (tensorCapND δ k₁) (tensorCapND δ k₂)
    ψ (fun w => conj (ψ w))
    (fun q => sourceAngularTransformND ρ (treeCell row.1) M₁ b q.1 q.2)
    (fun q => sourceAngularTransformND κ (treeCell col.2) M₂ c q.1 q.2)
    (fun q => sourceAngularTransformND κ (treeCell row.2) M₂ c q.1 q.2)
    (fun q => sourceAngularTransformND ρ (treeCell col.1) M₁ b q.1 q.2)
  have hr := Finset.mem_product.mp hr
  have hc := Finset.mem_product.mp hc
  by_cases h₁ : row.1 ∈ eligibleCells ρ a p X (tensorCapND δ k₁) b
  · by_cases h₂ : col.2 ∈ eligibleCells κ a p Y (tensorCapND δ k₁) c
    · by_cases h₃ : row.2 ∈ eligibleCells κ a p Y (tensorCapND δ k₂) c
      · exact Or.inr (Or.inr (Or.inr (graph_cell_cap_ineligible ρ hc.1 M₁ δ k₂ hb
          (fun h₄ => hin ⟨Finset.mem_product.mpr ⟨h₁,h₃⟩,Finset.mem_product.mpr ⟨h₄,h₂⟩⟩))))
      · exact Or.inr (Or.inr (Or.inl (graph_cell_cap_ineligible κ hr.2 M₂ δ k₂ hcj h₃)))
    · exact Or.inr (Or.inl (graph_cell_cap_ineligible κ hc.2 M₂ δ k₁ hcj h₂))
  · exact Or.inl (graph_cell_cap_ineligible ρ hr.1 M₁ δ k₁ hb h₁)

end CurrentFalconer.TreeND
end
end

end OAI
