import OAI.Geometry.Relativity.CKS.MixedSqrtJet

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev LapseCoefficientInput := ℝ × ScalarJet × ScalarJet × ScalarJet
abbrev lz (p : LapseCoefficientInput) := p.1
abbrev lT (p : LapseCoefficientInput) := p.2.1
abbrev lF (p : LapseCoefficientInput) := p.2.2.1
abbrev lD (p : LapseCoefficientInput) := p.2.2.2

def lapseV (p : LapseCoefficientInput) : ScalarJet :=
  (1/(1+lz p^2)) • ((2:ℝ) • lT p+lz p^3 • productJet (lT p) (lT p)-(2:ℝ) • lF p)
def lapseRad (p : LapseCoefficientInput) : ScalarJet := constantJet 1+lz p^3 • lapseV p
def lapseD (p : LapseCoefficientInput) : ScalarJet := constantJet 1+lz p^3 • lD p

def lapseA (p : LapseCoefficientInput) : ScalarJet :=
  productJet (productJet (lapseV p) (reciprocalJet (sqrtJet (lapseRad p)+constantJet 1))-lD p)
    (reciprocalJet (lapseD p))
def lapseCoefficientRegion : Set LapseCoefficientInput :=
  {p | 0 < (lapseRad p).1 ∧ (lapseD p).1 ≠ 0}
lemma lapseV_smooth : ContDiff ℝ ∞ lapseV := by
  have hp : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => productJet (lT p) (lT p)) :=
    productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => (lT p,lT p)))
  unfold lapseV
  exact ((contDiff_const.fun_div (by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => 1+lz p^2)) (by intro p; positivity))).fun_smul
    (((by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => (2:ℝ) • lT p)).add
      ((by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => lz p^3)).fun_smul hp)).sub (by fun_prop))
lemma lapseRad_smooth : ContDiff ℝ ∞ lapseRad :=
  contDiff_const.add ((by fun_prop : ContDiff ℝ ∞ (fun p : LapseCoefficientInput => lz p^3)).fun_smul lapseV_smooth)
lemma lapseD_smooth : ContDiff ℝ ∞ lapseD := by unfold lapseD; fun_prop
lemma lapseA_smooth {p : LapseCoefficientInput} (hp : p ∈ lapseCoefficientRegion) :
    ContDiffAt ℝ ∞ lapseA p := by
  have hs := (sqrtJet_smooth hp.1).comp p lapseRad_smooth.contDiffAt
  have hs1 := hs.add (contDiffAt_const (c := constantJet 1))
  have hs0 : (sqrtJet (lapseRad p)+constantJet 1).1 ≠ 0 := by
    change Real.sqrt (lapseRad p).1+1 ≠ 0
    positivity
  have hi := (reciprocalJet_smooth hs0).comp p hs1
  have hvi : ContDiffAt ℝ ∞ (fun p : LapseCoefficientInput =>
      productJet (lapseV p) (reciprocalJet (sqrtJet (lapseRad p)+constantJet 1))) p :=
    productJet_smooth.contDiffAt.comp p (lapseV_smooth.contDiffAt.prodMk hi)
  exact productJet_smooth.contDiffAt.comp p
    ((hvi.sub (by fun_prop)).prodMk ((reciprocalJet_smooth hp.2).comp p lapseD_smooth.contDiffAt))
lemma lapseCoefficientRegion_open : IsOpen lapseCoefficientRegion :=
  (isOpen_lt continuous_const (continuous_fst.comp lapseRad_smooth.continuous)).inter
    (isOpen_ne_fun (continuous_fst.comp lapseD_smooth.continuous) continuous_const)
lemma lapseCoefficientRegion_zero (T F D : ScalarJet) : (0,T,F,D) ∈ lapseCoefficientRegion := by
  simp [lapseCoefficientRegion,lapseRad,lapseD,constantJet,lz]

lemma lapseA_identity {p : LapseCoefficientInput} (hp : p ∈ lapseCoefficientRegion) :
    Real.sqrt ((lz p^2+(1+lz p^3*(lT p).1)^2-2*lz p^3*(lF p).1)/(1+lz p^2)) /
      (1+lz p^3*(lD p).1) = 1+lz p^3*(lapseA p).1 := by
  have hrad : (lz p^2+(1+lz p^3*(lT p).1)^2-2*lz p^3*(lF p).1)/(1+lz p^2) =
      (lapseRad p).1 := by
    simp only [lapseRad,lapseV,Prod.fst_add,Prod.fst_sub,Prod.smul_fst,smul_eq_mul,constantJet,productJet]
    have hz : 1+lz p^2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hrad]
  have hden : 1+lz p^3*(lD p).1 ≠ 0 := hp.2
  have hs : Real.sqrt (lapseRad p).1+1 ≠ 0 := by positivity
  have he : Real.sqrt (lapseRad p).1^2 = 1+lz p^3*(lapseV p).1 := Real.sq_sqrt hp.1.le
  change Real.sqrt (lapseRad p).1/(1+lz p^3*(lD p).1) =
    1+lz p^3*(((lapseV p).1*(1/(Real.sqrt (lapseRad p).1+1))-(lD p).1)*(1/(1+lz p^3*(lD p).1)))
  field_simp
  linear_combination he

lemma lapseCoefficient_uniform (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0, ∃ M : ℝ, 0 ≤ M ∧
      ∀ p p₀ : LapseCoefficientInput, |lz p| ≤ δ → |lz p₀| ≤ δ →
      ‖p.2‖ ≤ B → ‖p₀.2‖ ≤ B →
      p ∈ lapseCoefficientRegion ∧ ‖lapseA p‖ ≤ M ∧
        ‖lapseA p-lapseA p₀‖ ≤ (C:ℝ)*‖p-p₀‖ := by
  let K : Set LapseCoefficientInput := (fun t : ScalarJet × ScalarJet × ScalarJet => ((0:ℝ),t)) '' Metric.closedBall 0 B
  have hK : IsCompact K := (isCompact_closedBall 0 B).image (by fun_prop)
  have hKreg : K ⊆ lapseCoefficientRegion := by
    rintro p ⟨⟨T,F,D⟩,ht,rfl⟩
    exact lapseCoefficientRegion_zero T F D
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open lapseCoefficientRegion_open hKreg
  have hk := hK.cthickening (r := δ)
  obtain ⟨C,hC⟩ : ∃ C, LipschitzOnWith C lapseA (Metric.cthickening δ K) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hk
    intro p hp
    obtain ⟨C,t,ht,hC⟩ := ((lapseA_smooth (hsub hp)).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  obtain ⟨M,hM⟩ := hk.exists_bound_of_continuousOn
    (fun p hp => (lapseA_smooth (hsub hp)).continuousAt.continuousWithinAt)
  have hmem (p : LapseCoefficientInput) (hz : |lz p| ≤ δ) (ht : ‖p.2‖ ≤ B) :
      p ∈ Metric.cthickening δ K := by
    apply Metric.mem_cthickening_of_dist_le p (0,p.2) δ K
    · exact ⟨p.2,by simpa [Metric.mem_closedBall,dist_zero_right] using ht,rfl⟩
    · simpa only [Prod.dist_eq,dist_zero_right,dist_self,Real.norm_eq_abs,max_eq_left (abs_nonneg (p.1)),lz] using hz
  refine ⟨δ,hδ,C,max M 0,le_max_right _ _,?_⟩
  intro p p₀ hz hz₀ ht ht₀
  have hp := hmem p hz ht
  have hp₀ := hmem p₀ hz₀ ht₀
  refine ⟨hsub hp,(hM p hp).trans (le_max_left _ _),?_⟩
  simpa only [dist_eq_norm] using hC.dist_le_mul p hp p₀ hp₀

end
end CKSAngularGeometry

end

end OAI
