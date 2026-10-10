import Mathlib
import OAI.Geometry.BallPacking.Rigidity.AngularPoles

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)

theorem radialPrimitiveCLM_eq_moment {n : ℕ} (S T : ℝ) {x : Phase n}
    (hx : x ≠ 0) :
    radialPrimitiveCLM S T x = radialMoment S T (capacity x) • normalizedPrimitive x := by
  unfold radialPrimitiveCLM normalizedPrimitive radialMoment
  rw [smul_smul]
  congr 1
  have hn := (capacity_pos hx).ne'
  field_simp

theorem capacity_tendsto_atTop (n : ℕ) :
    Tendsto (@capacity n) (cocompact (Phase n)) atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(closedBall_isCompact n b).compl_mem_cocompact] with x hx
  have hx' : ¬ capacity x ≤ b := hx
  exact (lt_of_not_ge hx').le

theorem AffineLineCurve.radial_infinity_limit {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {S T : ℝ} (hST : S < T) :
    Tendsto (fun z : Plane => planarPullback (realCurve u) (radialPrimitiveCLM S T) z
      (planeRotation z)) (cocompact Plane) (𝓝 (1 / (2 * Real.pi))) := by
  obtain ⟨v,hv,hh,_⟩ := hu.analytic_at_infinity hJc
  have hr : Tendsto Complex.equivRealProdCLM.symm (cocompact Plane) (cocompact ℂ) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have hul : Tendsto (realCurve u) (cocompact Plane) (cocompact (Phase n)) :=
    hu.tendsto_cocompact.comp hr
  have hn : Tendsto (fun z : Plane => planarPullback (realCurve u) normalizedPrimitive z
      (planeRotation z)) (cocompact Plane) (𝓝 (1 / (2 * Real.pi))) := by
    have ht := (normalizedPrimitive_infinity_limit hv hh).comp hr
    apply ht.congr
    intro z
    change normalizedPrimitive _ _ = normalizedPrimitive _ _
    have he := realCurve_fderiv (z := z) ((hu.1.differentiable (by simp)) _) (planeRotation z)
    rw [equivRealProd_rotation] at he
    exact congrArg (normalizedPrimitive (u (Complex.equivRealProdCLM.symm z))) he.symm
  have hm : Tendsto (fun z : Plane => radialMoment S T (capacity (realCurve u z)))
      (cocompact Plane) (𝓝 1) :=
    (radialMoment_tendsto_one hST).comp ((capacity_tendsto_atTop n).comp hul)
  have ht : Tendsto (fun z : Plane => radialMoment S T (capacity (realCurve u z)) *
      planarPullback (realCurve u) normalizedPrimitive z (planeRotation z))
      (cocompact Plane) (𝓝 (1 / (2 * Real.pi))) := by
    simpa only [one_mul] using hm.mul hn
  apply ht.congr'
  filter_upwards [hul.eventually (isCompact_singleton (x := (0 : Phase n))).compl_mem_cocompact] with z hz
  unfold planarPullback
  rw [radialPrimitiveCLM_eq_moment S T hz]
  rfl

theorem correctedPrimitive_eq_radial_at_infinity {n : ℕ} (S T : ℝ)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i) :
    correctedPrimitive S T U f σ τ =ᶠ[cocompact (Phase n)] radialPrimitiveCLM S T := by
  have hc (i : Fin 2) := chartCorrection_compact (hf i) (hτ i) (hστ i) (hsub i)
  filter_upwards [(hc 0).compl_mem_cocompact,(hc 1).compl_mem_cocompact] with y hy0 hy1
  have h0 := image_eq_zero_of_notMem_tsupport hy0
  have h1 := image_eq_zero_of_notMem_tsupport hy1
  simp only [correctedPrimitive,h0,h1,add_zero]

theorem AffineLineCurve.corrected_infinity_limit {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {S T : ℝ} (hST : S < T)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i) :
    Tendsto (fun z : Plane => planarPullback (realCurve u) (correctedPrimitive S T U f σ τ) z
      (planeRotation z)) (cocompact Plane) (𝓝 (1 / (2 * Real.pi))) := by
  apply (hu.radial_infinity_limit hJc hST).congr'
  have hr : Tendsto Complex.equivRealProdCLM.symm (cocompact Plane) (cocompact ℂ) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have hul : Tendsto (realCurve u) (cocompact Plane) (cocompact (Phase n)) :=
    hu.tendsto_cocompact.comp hr
  filter_upwards [hul.eventually (correctedPrimitive_eq_radial_at_infinity S T hf hτ hστ hsub)] with z hz
  unfold planarPullback
  rw [hz]


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

theorem AffineLineCurve.finite_real_centre_fibre {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u)
    (hJ : ∀ᶠ y in 𝓝 (f 0), J y = imageJ U f y) :
    Set.Finite {z : Plane | realCurve u z = f 0} :=
  (hu.finite_centre_fibre hf h0 hJ).preimage Complex.equivRealProdCLM.symm.injective.injOn

theorem two_ball_line_area {n : ℕ} {S T : ℝ} (hST : S < T) (hT : T < 1)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hσ : ∀ i, 0 < σ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    (hdis : Disjoint (f 0 '' closedBall n (τ 0)) (f 1 '' closedBall n (τ 1)))
    (hcap : ∀ i, MapsTo (f i) (closedBall n (τ i)) (closedBall n S))
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (hout : ∀ x, S < capacity x → J x = standardJ n)
    (hJi : ∀ i, ∀ y ∈ f i '' closedBall n (τ i), J y = imageJ (U i) (f i) y)
    (hJnear : ∀ i, ∀ᶠ y in 𝓝 (f i 0), J y = imageJ (U i) (f i) y)
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {u : ℂ → Phase n} (hu : AffineLineCurve J (f 0 0) (f 1 0) u) :
    blowupSize (σ 0) (τ 0) + blowupSize (σ 1) (τ 1) ≤ 1 := by
  classical
  have hτ (i : Fin 2) : 0 < τ i := (hσ i).trans (hστ i)
  have hball0 (i : Fin 2) : (0 : Phase n) ∈ closedBall n (τ i) := by
    simpa [closedBall,capacity] using (hτ i).le
  have hne : f 0 0 ≠ f 1 0 := by
    intro he
    exact disjoint_left.mp hdis (mem_image_of_mem _ (hball0 0))
      (he.symm ▸ mem_image_of_mem (f 1) (hball0 1))
  have hfin (i : Fin 2) : Set.Finite {z : Plane | realCurve u z = f i 0} :=
    hu.finite_real_centre_fibre (hf i) (hsub i (hball0 i)) (hJnear i)
  let P := ((hfin 0).union (hfin 1)).toFinset
  have hP (z : Plane) : z ∈ P ↔ realCurve u z = f 0 0 ∨ realCurve u z = f 1 0 := by
    simp only [P,Set.Finite.mem_toFinset,Set.mem_union,Set.mem_ofPred_eq]
  let idx (z : Plane) : Fin 2 := if realCurve u z = f 0 0 then 0 else 1
  have hidx (z : Plane) (hz : z ∈ P) : realCurve u z = f (idx z) 0 := by
    unfold idx
    split_ifs with h
    · exact h
    · exact ((hP z).mp hz).resolve_left h
  let α := planarPullback (realCurve u) (correctedPrimitive S T U f σ τ)
  have hres (z : Plane) (hz : z ∈ P) : ∃ m : ℕ, 0 < m ∧
      ∃ β : Plane → Plane →L[ℝ] ℝ, ContDiffAt ℝ ∞ β z ∧
        α =ᶠ[𝓝[≠] z] fun w => ((blowupSize (σ (idx z)) (τ (idx z)) * (m:ℝ)) /
          (2 * Real.pi)) • angularPole z w + β w := by
    have hh := correctedPrimitive_centre_residue hST hf hσ hστ hsub hne hu hJnear
      (idx z) (a := Complex.equivRealProdCLM.symm z) (hidx z hz)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,α,Filter.EventuallyEq] using hh
  choose m hm β hβs hβe using hres
  let c (z : Plane) : ℝ := if hz : z ∈ P then
    blowupSize (σ (idx z)) (τ (idx z)) * (m z hz : ℝ) / (2 * Real.pi) else 0
  have hc (z : Plane) (hz : z ∈ P) :
      c z = blowupSize (σ (idx z)) (τ (idx z)) * (m z hz : ℝ) / (2 * Real.pi) := dite_eq_left hz
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hsize (i : Fin 2) : 0 < blowupSize (σ i) (τ i) :=
    (hσ i).trans_le (blowupSize_bounds (hστ i)).1
  have hcnon (z : Plane) : 0 ≤ c z := by
    by_cases hz : z ∈ P
    · rw [hc z hz]
      exact div_nonneg (mul_nonneg (hsize _).le (Nat.cast_nonneg _)) hpi.le
    · simp only [c,dite_eq_right hz,le_refl]
  have hclower (z : Plane) (hz : z ∈ P) :
      blowupSize (σ (idx z)) (τ (idx z)) / (2 * Real.pi) ≤ c z := by
    rw [hc z hz]
    apply div_le_div_of_nonneg_right _ hpi.le
    exact le_mul_of_one_le_right (hsize _).le (by exact_mod_cast (Nat.succ_le_iff.mpr (hm z hz)))
  have haway (z : Plane) (hz : z ∉ P) : ∀ i : Fin 2, realCurve u z ≠ f i 0 := by
    intro i
    fin_cases i
    · exact fun he => hz ((hP z).mpr (Or.inl he))
    · exact fun he => hz ((hP z).mpr (Or.inr he))
  have hsum : (∑ z ∈ P, c z) ≤ 1 / (2 * Real.pi) := by
    apply finite_residues_le_infinity P c α
    · intro z hz
      exact planarPullback_smoothAt (realCurve_smooth hu.1).contDiffAt
        (correctedPrimitive_smoothAt hST hf hτ hστ hsub (haway z hz))
    · intro z hz
      exact correctedCurve_curl_nonneg hST hT hf hτ hστ hsub hdis hcap hJ hout hJi
        hu.1 hu.2.1 (haway z hz)
    · intro z hz
      refine ⟨β z hz,hβs z hz,?_⟩
      rw [hc z hz]
      exact hβe z hz
    · exact hu.corrected_infinity_limit hJc hST hf hτ hστ hsub
  have hu0 : realCurve u 0 = f 0 0 := by simpa only [realCurve_zero] using hu.2.2.1
  have hu1 : realCurve u (1,0) = f 1 0 := by
    simpa only [realCurve,Function.comp_def,Complex.equivRealProdCLM_symm_apply,
      Complex.ofReal_one,Complex.ofReal_zero,zero_mul,add_zero] using hu.2.2.2.1
  have hp0 : (0 : Plane) ∈ P := (hP 0).mpr (Or.inl hu0)
  have hp1 : (1,0) ∈ P := (hP (1,0)).mpr (Or.inr hu1)
  have hi0 : idx 0 = 0 := ite_eq_left hu0
  have hi1 : idx (1,0) = 1 := ite_eq_right (by rw [hu1]; exact hne.symm)
  have hs01 : c 0 + c (1,0) ≤ ∑ z ∈ P, c z := by
    have hsubP : ({0,(1,0)} : Finset Plane) ⊆ P := by
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hp0
      · exact hp1
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsubP (fun z _ _ => hcnon z)
    have h01 : (0 : Plane) ≠ (1,0) := by
      intro he
      have hh := congrArg Prod.fst he
      norm_num at hh
    rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using h01),Finset.sum_singleton] at hs
    exact hs
  have hlow0 := hclower 0 hp0
  have hlow1 := hclower (1,0) hp1
  rw [hi0] at hlow0
  rw [hi1] at hlow1
  apply (div_le_div_iff_of_pos_right hpi).mp
  rw [add_div]
  linarith


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem two_ball_capacity_of_adapted_line {n : ℕ} {S T : ℝ} (hST : S < T) (hT : T < 1)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {r : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hr : ∀ i, 0 < r i)
    (hsub : ∀ i, closedBall n (r i) ⊆ U i)
    (hdis : Disjoint (f 0 '' closedBall n (r 0)) (f 1 '' closedBall n (r 1)))
    (hcap : ∀ i, MapsTo (f i) (closedBall n (r i)) (closedBall n S))
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (hout : ∀ x, S < capacity x → J x = standardJ n)
    (hJi : ∀ i, ∀ y ∈ f i '' closedBall n (r i), J y = imageJ (U i) (f i) y)
    (hJnear : ∀ i, ∀ᶠ y in 𝓝 (f i 0), J y = imageJ (U i) (f i) y)
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {u : ℂ → Phase n} (hu : AffineLineCurve J (f 0 0) (f 1 0) u) :
    r 0 + r 1 ≤ 1 := by
  by_contra! hlarge
  let δ := min (r 0) (min (r 1) (r 0 + r 1 - 1)) / 4
  have hδ : 0 < δ := div_pos (lt_min (hr 0) (lt_min (hr 1) (by linarith))) (by norm_num)
  have hδ0 : 4*δ ≤ r 0 := by
    dsimp [δ]
    linarith only [min_le_left (r 0) (min (r 1) (r 0+r 1-1))]
  have hδ1 : 4*δ ≤ r 1 := by
    have h := (min_le_right (r 0) (min (r 1) (r 0+r 1-1))).trans
      (min_le_left (r 1) (r 0+r 1-1))
    dsimp [δ]
    linarith only [h]
  have hδsum : 4*δ ≤ r 0+r 1-1 := by
    have h := (min_le_right (r 0) (min (r 1) (r 0+r 1-1))).trans
      (min_le_right (r 1) (r 0+r 1-1))
    dsimp [δ]
    linarith only [h]
  have hσ (i : Fin 2) : 0 < r i - δ := by
    fin_cases i <;> simp only [Fin.mk_zero,Fin.mk_one] <;> linarith
  have hστ (i : Fin 2) : r i - δ < r i := by linarith
  have harea := two_ball_line_area hST hT hf hσ hστ hsub hdis hcap hJ hout hJi hJnear hJc hu
  have h0 := (blowupSize_bounds (hστ 0)).1
  have h1 := (blowupSize_bounds (hστ 1)).1
  linarith




theorem packing_two_line_reduction {n : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp : HasPacking n 2 1 ![a,b]) :
    ∃ (J : Phase n → End n) (p q : Phase n), ContDiff ℝ ∞ J ∧
      (∀ x, Compatible (J x)) ∧ HasCompactSupport (fun x => J x - standardJ n) ∧
      tsupport (fun x => J x - standardJ n) ⊆ openBall n 1 ∧ p ≠ q ∧
      ∀ u : ℂ → Phase n, AffineLineCurve J p q u → a+b ≤ 1 := by
  obtain ⟨U,f,J,hf,hd,hJs,hJ,hJn,hJc,hJsupp⟩ := packing_two_has_adapted_structure hp
  let r : Fin 2 → ℝ := ![a,b]
  have hr (i : Fin 2) : 0 < r i := by
    fin_cases i
    · exact ha
    · exact hb
  have h0 (i : Fin 2) : (0 : Phase n) ∈ closedBall n (r i) := by
    simpa [closedBall,capacity] using (hr i).le
  have hne : f 0 0 ≠ f 1 0 := by
    intro he
    exact disjoint_left.mp (hd 0 1 (by decide)) (mem_image_of_mem _ (h0 0))
      (he.symm ▸ mem_image_of_mem (f 1) (h0 1))
  refine ⟨J,f 0 0,f 1 0,hJs,hJ,hJc,hJsupp,hne,?_⟩
  intro u hu
  let K := tsupport (fun x => J x - standardJ n) ∪
    (f 0 '' closedBall n (r 0)) ∪ (f 1 '' closedBall n (r 1))
  have hKi (i : Fin 2) : IsCompact (f i '' closedBall n (r i)) :=
    (closedBall_isCompact n (r i)).image_of_continuousOn ((hf i).2.1.2.1.continuousOn.mono (hf i).1)
  have hK : IsCompact K := (hJc.union (hKi 0)).union (hKi 1)
  have hmemK (i : Fin 2) {x : Phase n} (hx : x ∈ closedBall n (r i)) : f i x ∈ K := by
    fin_cases i
    · exact Or.inl (Or.inr ⟨x,hx,rfl⟩)
    · exact Or.inr ⟨x,hx,rfl⟩
  have hKopen : K ⊆ openBall n 1 := by
    rintro y ((hy | hy) | hy)
    · exact hJsupp hy
    · obtain ⟨x,hx,rfl⟩ := hy
      exact (hf 0).2.2 hx
    · obtain ⟨x,hx,rfl⟩ := hy
      exact (hf 1).2.2 hx
  obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn ⟨f 0 0,hmemK 0 (h0 0)⟩
    (capacity_smooth n).continuous.continuousOn
  let S := capacity x
  let T := (S+1)/2
  have hS : S < 1 := hKopen hx
  have hST : S < T := by dsimp [T]; linarith
  have hT : T < 1 := by dsimp [T]; linarith
  have hcap (i : Fin 2) : MapsTo (f i) (closedBall n (r i)) (closedBall n S) := by
    intro y hy
    exact hmax (hmemK i hy)
  have hout (y : Phase n) (hy : S < capacity y) : J y = standardJ n := by
    have hn : y ∉ tsupport (fun z => J z - standardJ n) := by
      intro hyK
      exact (not_le_of_gt hy) (hmax (Or.inl (Or.inl hyK)))
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun z => J z - standardJ n) hn)
  have hJi (i : Fin 2) (y : Phase n) (hy : y ∈ f i '' closedBall n (r i)) :
      J y = imageJ (U i) (f i) y :=
    ((hJn i).filter_mono (nhds_le_nhdsSet hy)).self_of_nhds
  have hJnear (i : Fin 2) : ∀ᶠ y in 𝓝 (f i 0), J y = imageJ (U i) (f i) y :=
    (hJn i).filter_mono (nhds_le_nhdsSet (mem_image_of_mem _ (h0 i)))
  exact two_ball_capacity_of_adapted_line hST hT (fun i => (hf i).2.1) hr
    (fun i => (hf i).1) (hd 0 1 (by decide)) hcap hJ hout hJi hJnear hJc hu



end HigherDimensionalBallPacking.Rigidity
end

end OAI
