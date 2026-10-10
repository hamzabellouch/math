import OAI.Analysis.KadisonKastler.TwoRatioFiniteMatrix
import OAI.Analysis.KadisonKastler.MatrixProductStateSwap

namespace OAI

/-! # The weighted trace identity at a matrix site

Product moments identify the two weights in the KMS balance equation.
The identity is first proved in a finite block containing the site, then
extended to the actual von Neumann closure by strong density.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H} {ν : I → ℝ}

theorem weighted_productState_generated
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (u : H →L[ℂ] H)
    (c d : ℂ)
    (hA : ∀ x ∈ A, c * productVectorState Ω (u * x) =
      d * productVectorState Ω (x * u)) :
    ∀ x ∈ generatedVonNeumannAlgebra A,
      c * productVectorState Ω (u * x) = d * productVectorState Ω (x * u) := by
  classical
  intro x hx
  have hx' : x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
    rwa [← generatedVonNeumannAlgebra_coe]
  obtain ⟨a, ha⟩ := Generator.bicommutant_exists_strong_net A x hx'
  have hl : Tendsto (fun k => c * productVectorState Ω (u * (a k : H →L[ℂ] H)))
      atTop (𝓝 (c * productVectorState Ω (u * x))) := by
    apply tendsto_const_nhds.mul
    change Tendsto (fun k => inner ℂ Ω (u ((a k : H →L[ℂ] H) Ω))) atTop
      (𝓝 (inner ℂ Ω (u (x Ω))))
    exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp
      (u.continuous.continuousAt.tendsto.comp (ha Ω))
  have hr : Tendsto (fun k => d * productVectorState Ω ((a k : H →L[ℂ] H) * u))
      atTop (𝓝 (d * productVectorState Ω (x * u))) := by
    apply tendsto_const_nhds.mul
    change Tendsto (fun k => inner ℂ Ω ((a k : H →L[ℂ] H) (u Ω))) atTop
      (𝓝 (inner ℂ Ω (x (u Ω))))
    exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp (ha (u Ω))
  exact tendsto_nhds_unique (hl.congr fun k => hA _ (a k).property) hr

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω ν)

theorem site_balance_blockEntry (i : I) (l : List I) (hl : l.Nodup) (hi : i ∉ l)
    (a b c d : Fin 2) (r s : MatrixSiteBlockIndex l) :
    (twoSiteWeight (ν i) b : ℂ) * productVectorState Ω
        ((S.site i).entry a b * S.blockEntry (i :: l) (c, r) (d, s)) =
      (twoSiteWeight (ν i) a : ℂ) * productVectorState Ω
        (S.blockEntry (i :: l) (c, r) (d, s) * (S.site i).entry a b) := by
  have hm (a b : Fin 2) :
      productVectorState Ω ((S.site i).entry a b * S.blockEntry l r s) =
        (if a = b then (twoSiteWeight (ν i) a : ℂ) else 0) *
          matrixSiteBlockWeight ν l r s :=
    S.blockEntry_moment (i :: l) (List.nodup_cons.mpr ⟨hi, hl⟩) (a, r) (b, s)
  change (twoSiteWeight (ν i) b : ℂ) * productVectorState Ω
      ((S.site i).entry a b * ((S.site i).entry c d * S.blockEntry l r s)) =
    (twoSiteWeight (ν i) a : ℂ) * productVectorState Ω
      (((S.site i).entry c d * S.blockEntry l r s) * (S.site i).entry a b)
  rw [← mul_assoc, mul_assoc ((S.site i).entry c d),
    ← (S.site_commutes_blockEntry i a b l hi r s).eq, ← mul_assoc]
  rw [(S.site i).mul_entry, (S.site i).mul_entry]
  have hz : productVectorState Ω (0 : H →L[ℂ] H) = 0 := by
    simp [productVectorState]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst c; subst d
    simp only [ite_true, hm]
    ring
  · simp [hbc, hda, hz, hm, Ne.symm hda]
  · simp [hbc, hda, hz, hm, Ne.symm hbc]
  · simp [hbc, hda, hz]

theorem site_balance_finiteBlock (i : I) (l : List I) (hl : l.Nodup) (hi : i ∉ l)
    (a b : Fin 2) (x : H →L[ℂ] H)
    (hx : x ∈ (S.finiteBlock (i :: l) (List.nodup_cons.mpr ⟨hi, hl⟩)).algebra) :
    (twoSiteWeight (ν i) b : ℂ) * productVectorState Ω ((S.site i).entry a b * x) =
      (twoSiteWeight (ν i) a : ℂ) * productVectorState Ω (x * (S.site i).entry a b) := by
  classical
  let E := S.finiteBlock (i :: l) (List.nodup_cons.mpr ⟨hi, hl⟩)
  obtain ⟨v, rfl⟩ := (E.mem_algebra x).mp hx
  let φ := productVectorLinear Ω
  have he (r s : MatrixSiteBlockIndex (i :: l)) :
      (twoSiteWeight (ν i) b : ℂ) * φ ((S.site i).entry a b * E.entry r s) =
        (twoSiteWeight (ν i) a : ℂ) * φ (E.entry r s * (S.site i).entry a b) :=
    S.site_balance_blockEntry i l hl hi a b r.1 s.1 r.2 s.2
  change (twoSiteWeight (ν i) b : ℂ) * φ ((S.site i).entry a b * _) =
    (twoSiteWeight (ν i) a : ℂ) * φ (_ * (S.site i).entry a b)
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    map_sum, map_smul, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (twoSiteWeight (ν i) b : ℂ), mul_assoc,
    he, ← mul_assoc]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- The weighted site identity holds against every operator in the product algebra. -/
theorem twoRatio_site_balance (T : PointedMatrixSites M Ω twoRatioSiteParameter)
    (i : TwoRatioSite) (a b : Fin 2) (x : H →L[ℂ] H) (hx : x ∈ M) :
    (twoSiteWeight (twoRatioSiteParameter i) b : ℂ) *
        productVectorState Ω ((T.site i).entry a b * x) =
      (twoSiteWeight (twoRatioSiteParameter i) a : ℂ) *
        productVectorState Ω (x * (T.site i).entry a b) := by
  classical
  rw [← T.twoRatioMatrix_generates] at hx
  apply weighted_productState_generated _ Ω ((T.site i).entry a b) _ _ ?_ x hx
  intro y hy
  have hym : y ∈ ⋃ n, ((T.twoRatioMatrix n).algebra : Set (H →L[ℂ] H)) := by
    rw [← StarSubalgebra.coe_iSup_of_directed T.twoRatioMatrix_increasing.directed_le]
    exact hy
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hym
  let l := (twoRatioFiniteSites n).filter (fun j => decide (j ≠ i))
  have hl : l.Nodup := (twoRatioFiniteSites_nodup n).filter _
  have hi : i ∉ l := by simp [l]
  apply T.site_balance_finiteBlock i l hl hi a b y
  have hle : (T.twoRatioMatrix n).algebra ≤
      (T.finiteBlock (i :: l) (List.nodup_cons.mpr ⟨hi, hl⟩)).algebra := by
    rw [T.twoRatioMatrix_algebra]
    apply T.finiteBlock_mono
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · apply List.mem_cons_of_mem i
      simpa [l] using And.intro hj hji
  exact hle hn

end PointedMatrixSites

end

end KadisonKastler

end OAI
