import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevContinuation

namespace OAI

/-!
# The maximal Sobolev interaction solution

Local solutions through the same initial datum agree on overlapping time
intervals. Their union therefore defines one classical solution on an open,
connected domain, containing every other solution interval through that datum.
-/

open Filter Topology Set

namespace DefocusingNLS

/-- A classical solution patch on an open interval containing the initial time. -/
structure SobolevInteractionPatch (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) where
  left : ℝ
  right : ℝ
  left_neg : left < 0
  right_pos : 0 < right
  curve : ℝ → FourierL2
  initial : curve 0 = f₀
  solves : ∀ t ∈ Ioo left right,
    HasDerivAt curve (schrodingerInteractionField k hk m t (curve t)) t

theorem sobolevInteractionPatch_nonempty (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) :
    Nonempty (SobolevInteractionPatch k hk m f₀) := by
  obtain ⟨T, hT, v, hv₀, hv⟩ := exists_sobolevInteractionSolution k hk m f₀
  exact ⟨⟨-T, T, by linarith, hT, v, hv₀, hv⟩⟩

/-- The union of every classical solution interval through the prescribed datum. -/
def maximalSobolevInteractionDomain (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) : Set ℝ :=
  ⋃ P : SobolevInteractionPatch k hk m f₀, Ioo P.left P.right

/-- The unique value supplied by any classical solution patch containing the time. -/
noncomputable def maximalSobolevInteractionFlow (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) (t : ℝ) : FourierL2 := by
  classical
  exact if ht : t ∈ maximalSobolevInteractionDomain k hk m f₀ then
    (Classical.choose (mem_iUnion.mp ht)).curve t
  else 0

/-- Any two local patches agree wherever their intervals overlap. -/
theorem SobolevInteractionPatch.eqOn_overlap
    {k : ℝ} {hk : 6 < k} {m : ℕ} {f₀ : FourierL2}
    (P Q : SobolevInteractionPatch k hk m f₀) :
    EqOn P.curve Q.curve (Ioo (max P.left Q.left) (min P.right Q.right)) := by
  apply sobolevInteractionSolution_unique_on_interval k hk m P.curve Q.curve
    (max P.left Q.left) (min P.right Q.right) 0
    ⟨max_lt P.left_neg Q.left_neg, lt_min P.right_pos Q.right_pos⟩
  · intro t ht
    exact P.solves t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  · intro t ht
    exact Q.solves t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  · exact P.initial.trans Q.initial.symm

/-- The maximal solution agrees with each of its classical patches. -/
theorem maximalSobolevInteractionFlow_eq_patch
    {k : ℝ} {hk : 6 < k} {m : ℕ} {f₀ : FourierL2}
    (P : SobolevInteractionPatch k hk m f₀) {t : ℝ} (ht : t ∈ Ioo P.left P.right) :
    maximalSobolevInteractionFlow k hk m f₀ t = P.curve t := by
  have hdom : t ∈ maximalSobolevInteractionDomain k hk m f₀ := mem_iUnion.mpr ⟨P, ht⟩
  rw [maximalSobolevInteractionFlow, dite_eq_left hdom]
  let Q := Classical.choose (mem_iUnion.mp hdom)
  have hQ : t ∈ Ioo Q.left Q.right := Classical.choose_spec (mem_iUnion.mp hdom)
  exact Q.eqOn_overlap P ⟨max_lt hQ.1 ht.1, lt_min hQ.2 ht.2⟩

theorem isOpen_maximalSobolevInteractionDomain (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) : IsOpen (maximalSobolevInteractionDomain k hk m f₀) :=
  isOpen_iUnion (fun _ => isOpen_Ioo)

theorem zero_mem_maximalSobolevInteractionDomain (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) : 0 ∈ maximalSobolevInteractionDomain k hk m f₀ := by
  obtain ⟨P⟩ := sobolevInteractionPatch_nonempty k hk m f₀
  exact mem_iUnion.mpr ⟨P, P.left_neg, P.right_pos⟩

theorem isPreconnected_maximalSobolevInteractionDomain (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) : IsPreconnected (maximalSobolevInteractionDomain k hk m f₀) := by
  apply isPreconnected_iUnion
  · refine ⟨0, mem_iInter.mpr (fun P => ?_)⟩
    exact ⟨P.left_neg, P.right_pos⟩
  · intro P
    exact isPreconnected_Ioo

@[simp] theorem maximalSobolevInteractionFlow_initial (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) : maximalSobolevInteractionFlow k hk m f₀ 0 = f₀ := by
  obtain ⟨P⟩ := sobolevInteractionPatch_nonempty k hk m f₀
  rw [maximalSobolevInteractionFlow_eq_patch P ⟨P.left_neg, P.right_pos⟩, P.initial]

/-- The union is a classical solution at every point of its maximal open domain. -/
theorem hasDerivAt_maximalSobolevInteractionFlow (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f₀ : FourierL2) {t : ℝ} (ht : t ∈ maximalSobolevInteractionDomain k hk m f₀) :
    HasDerivAt (maximalSobolevInteractionFlow k hk m f₀)
      (schrodingerInteractionField k hk m t (maximalSobolevInteractionFlow k hk m f₀ t)) t := by
  obtain ⟨P, hP⟩ := mem_iUnion.mp ht
  have he : maximalSobolevInteractionFlow k hk m f₀ =ᶠ[𝓝 t] P.curve := by
    filter_upwards [isOpen_Ioo.mem_nhds hP] with s hs
    exact maximalSobolevInteractionFlow_eq_patch P hs
  rw [maximalSobolevInteractionFlow_eq_patch P hP]
  exact (P.solves t hP).congr_of_eventuallyEq he

/-- Every solution interval through the datum is contained in this domain. -/
theorem SobolevInteractionPatch.subset_maximalDomain
    {k : ℝ} {hk : 6 < k} {m : ℕ} {f₀ : FourierL2}
    (P : SobolevInteractionPatch k hk m f₀) :
    Ioo P.left P.right ⊆ maximalSobolevInteractionDomain k hk m f₀ := by
  intro t ht
  exact mem_iUnion.mpr ⟨P, ht⟩

end DefocusingNLS

end OAI
