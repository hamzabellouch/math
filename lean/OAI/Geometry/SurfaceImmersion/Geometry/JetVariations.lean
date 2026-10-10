import OAI.Geometry.SurfaceImmersion.Atlas.WeightedActualJets

namespace OAI

/-! Actual variations of the ordered coordinate jets. The position entries
do not vary, and a second-jet variation costs at most two short-scale powers. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma directional_add {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : A → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : List A) :
    iteratedDirectional w (fun x => f x + g x) =
      fun x => iteratedDirectional w f x + iteratedDirectional w g x := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [iteratedDirectional, ih]
    funext x
    have hfs := contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hf.contDiffOn w)
    have hgs := contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hg.contDiffOn w)
    rw [fderiv_fun_add (hfs.differentiable (by simp) x) (hgs.differentiable (by simp) x),
      add_apply]

lemma directional_smul {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : A → E}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (w : List A) :
    iteratedDirectional w (fun x => c • f x) = fun x => c • iteratedDirectional w f x := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [iteratedDirectional, ih]
    funext x
    have hfs := contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hf.contDiffOn w)
    exact congrArg (fun L : A →L[ℝ] E => L v)
      (((hfs.differentiable (by simp) x).hasFDerivAt.const_smul c).fderiv)

lemma jet_add {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    jet (fun q => G q + H q) w a p = jet G w a p + jet H w a p :=
  congrFun (directional_add (contDiff_pi.mp hG a) (contDiff_pi.mp hH a)
    (w.map coordinateVector)) p

lemma jet_smul {H : Base → Space} (hH : ContDiff ℝ ∞ H)
    (c : ℝ) (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    jet (fun q => c • H q) w a p = c * jet H w a p :=
  congrFun (directional_smul (contDiff_pi.mp hH a) c (w.map coordinateVector)) p

def variationLowJet (H : Base → Space) (p : Base) : LowJet
  | .inl _ => 0
  | .inr (i, a) => jet H (lowWord i) a p

lemma variationLowJet_smooth {H : Base → Space} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (variationLowJet H) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact contDiff_const
  | inr i => exact jet_smooth hH (lowWord i.1) i.2

lemma lowJet_affine {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (t : ℝ) (p : Base) :
    lowJet (fun q => G q + t • H q) p = lowJet G p + t • variationLowJet H p := by
  funext i
  cases i with
  | inl i => simp [lowJet, variationLowJet]
  | inr i =>
    change jet (fun q => G q + t • H q) (lowWord i.1) i.2 p = _
    rw [jet_add (H := fun q => t • H q) hG (ContDiff.const_smul t hH), jet_smul hH]
    rfl

lemma lowJet_affine_hasDerivAt {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (p : Base) (t : ℝ) :
    HasDerivAt (fun s : ℝ => lowJet (fun q => G q + s • H q) p) (variationLowJet H p) t := by
  have he : (fun s : ℝ => lowJet (fun q => G q + s • H q) p) =
      (fun s : ℝ => lowJet G p + s • variationLowJet H p) :=
    funext (fun s => lowJet_affine hG hH s p)
  rw [he]
  simpa only [one_smul, id_eq] using
    ((hasDerivAt_id t).smul_const (variationLowJet H p)).const_add (lowJet G p)

theorem weighted_variationLowJet {U : Set Base} (hU : IsOpen U)
    {H : Base → Space} (hH : ContDiff ℝ ∞ H) {s C : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C) (m : ℕ)
    (hb : WeightedBound U s (m + 2) C H) :
    WeightedBound U s m (C / s ^ 2) (variationLowJet H) := by
  apply WeightedBound.pi hU.uniqueDiffOn hs (div_nonneg hC (sq_nonneg s))
    (fun i => (contDiff_pi.mp (variationLowJet_smooth hH) i).contDiffOn)
  intro i
  cases i with
  | inl i =>
    change WeightedBound U s m (C / s ^ 2) (fun _ => (0 : ℝ))
    exact (weightedBound_const U s m (0 : ℝ)).mono_const
      (by simpa only [norm_zero] using div_nonneg hC (sq_nonneg s))
  | inr i =>
    obtain ⟨w, a⟩ := i
    have hlen : (lowWord w).length ≤ 2 := by fin_cases w <;> simp [lowWord]
    have hc := hb.component hU.uniqueDiffOn hs.le hC hH.contDiffOn a
    have hbc : WeightedBound U s (m + ((lowWord w).map coordinateVector).length) C
        (fun p => H p a) := by
      simpa only [List.length_map] using hc.mono_order (Nat.add_le_add_left hlen m)
    have hd := hbc.iteratedDirectional hU hs hC
      (contDiff_pi.mp hH a).contDiffOn ((lowWord w).map coordinateVector)
      (fun v hv => by
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
        exact norm_coordinateVector_le j) m
    apply hd.mono_const
    apply div_le_div_of_nonneg_left hC (pow_pos hs 2)
    exact pow_le_pow_of_le_one hs.le hs1 (by simpa only [List.length_map] using hlen)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
