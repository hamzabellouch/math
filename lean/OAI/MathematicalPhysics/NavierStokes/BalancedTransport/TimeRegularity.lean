import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Work

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def JointSmooth (f : Field F) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)

theorem JointSmooth.slice {f : Field F} (hf : JointSmooth f) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (f t) := hf.comp (contDiff_const.prodMk contDiff_id)

theorem JointSmooth.spaceD {f : Field F} (hf : JointSmooth f) (i : Fin 3) :
    JointSmooth (spaceD i f) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (ℝ × Space) × Space => f z.1.1 z.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hh.fderiv_apply contDiff_snd contDiff_const (by simp)

theorem JointSmooth.curl {A : Velocity} (hA : JointSmooth A) :
    JointSmooth (fun t => curl (A t)) := by
  have he (i : Fin 3) : JointSmooth (fun t x => A t x i) := contDiff_pi.mp hA i
  have hd (i j : Fin 3) := (he j).spaceD i
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (hd 1 2).sub (hd 2 1)
  · exact (hd 2 0).sub (hd 0 2)
  · exact (hd 0 1).sub (hd 1 0)

theorem divergence_eq_div {A : Velocity} (hA : JointSmooth A) (t : ℝ) (x : Space) :
    divergence (A t) x = div A t x := by
  apply Finset.sum_congr rfl
  intro i _
  exact pd_apply i i ((hA.slice t).differentiable (by simp) x)

theorem JointSmooth.solenoidal_curl {A : Velocity} (hA : JointSmooth A)
    (t : ℝ) (x : Space) : div (fun s => Geometry.curl (A s)) t x = 0 := by
  rw [← divergence_eq_div hA.curl]
  exact divergence_curl (hA.slice t) x

def fullTimeD (f : Field F) : Field F := fun t x => deriv (fun s => f s x) t

theorem JointSmooth.fullTimeD {f : Field F} (hf : JointSmooth f) :
    JointSmooth (fullTimeD f) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (ℝ × Space) × ℝ => f z.2 z.1.2) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst.snd)
  exact ContDiff.fderiv_apply (f := fun z : ℝ × Space => fun s => f s z.2)
    hh contDiff_fst contDiff_const (by simp)

def lowerEndpoint (a : Space) (c d : ℝ → Space) (t : ℝ) : Space :=
  fun i => c t i + d t i * a i

def logarithmicRate (d : ℝ → Space) (t : ℝ) : Space :=
  fun i => deriv (fun s => d s i) t / d t i

def movingBoxVelocity (a b : Space) (c d : ℝ → Space) (η : ℝ) : Velocity :=
  fun t => localizedAffine (lowerEndpoint a c d t) (lowerEndpoint b c d t)
    (c t) (deriv c t) (logarithmicRate d t) η

lemma logarithmicRate_trace_zero {d : ℝ → Space} (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) (hdet : ∀ t, ∏ i, d t i = 1) (t : ℝ) :
    ∑ i, logarithmicRate d t i = 0 := by
  have dh (i : Fin 3) := ((contDiff_pi.mp hd i).differentiable (by simp) t).hasDerivAt
  have hconst : (fun s => d s 0 * d s 1 * d s 2) = fun _ => (1 : ℝ) := by
    funext s
    simpa [Fin.prod_univ_succ, mul_assoc] using hdet s
  have hh := ((dh 0).fun_mul (dh 1)).fun_mul (dh 2)
  rw [hconst] at hh
  have hz := hh.unique (hasDerivAt_const t (1 : ℝ))
  simp only [logarithmicRate, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change deriv (fun s => d s 0) t / d t 0 +
    (deriv (fun s => d s 1) t / d t 1 + deriv (fun s => d s 2) t / d t 2) = 0
  field_simp [hn t 0, hn t 1, hn t 2]
  nlinarith

lemma logarithmicRate_contDiff {d : ℝ → Space} (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) : ContDiff ℝ (⊤ : ℕ∞) (logarithmicRate d) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_infty_iff_deriv.mp (contDiff_pi.mp hd i)).2.div
    (contDiff_pi.mp hd i) (fun t => hn t i)

theorem movingBoxVelocity_jointSmooth {c d : ℝ → Space}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) (a b : Space) (η : ℝ) :
    JointSmooth (movingBoxVelocity a b c d η) := by
  apply JointSmooth.curl
  have hcd := (contDiff_infty_iff_deriv.mp hc).2
  have hl := logarithmicRate_contDiff hd hn
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Space =>
    boxCutoff (lowerEndpoint a c d z.1) (lowerEndpoint b c d z.1) η z.2 •
      affinePotential (c z.1) (deriv c z.1) (logarithmicRate d z.1) z.2)
  refine ContDiff.smul (f := fun z : ℝ × Space =>
    boxCutoff (lowerEndpoint a c d z.1) (lowerEndpoint b c d z.1) η z.2)
    (g := fun z : ℝ × Space =>
      affinePotential (c z.1) (deriv c z.1) (logarithmicRate d z.1) z.2) ?_ ?_
  · unfold boxCutoff lowerEndpoint
    fun_prop
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [affinePotential] <;> fun_prop

theorem movingBoxVelocity_divergence {c d : ℝ → Space}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) (a b : Space) (η t : ℝ) (x : Space) :
    div (movingBoxVelocity a b c d η) t x = 0 := by
  rw [← divergence_eq_div (movingBoxVelocity_jointSmooth hc hd hn a b η)]
  exact localizedAffine_divergence _ _ _ _ _ _ _

def affinePath (c d : ℝ → Space) (z : Space) (t : ℝ) : Space :=
  fun i => c t i + d t i * z i

lemma affinePath_mem_plateau {a b : Space} {c d : ℝ → Space} {η : ℝ}
    (hη : 0 < η) {z : Space} (hz : z ∈ Set.Icc a b) {t : ℝ}
    (hd : ∀ i, 0 < d t i) :
    affinePath c d z t ∈ openEnlargement (lowerEndpoint a c d t)
      (lowerEndpoint b c d t) η := by
  rw [mem_openEnlargement]
  intro i
  have hz₁ := hz.1 i
  have hz₂ := hz.2 i
  dsimp [lowerEndpoint, affinePath]
  constructor <;> nlinarith [hd i]

theorem affinePath_hasDerivAt_of_mem_plateau {a b : Space} {c d : ℝ → Space} {η : ℝ}
    (hη : 0 < η) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hp : ∀ t i, 0 < d t i) (hdet : ∀ t, ∏ i, d t i = 1)
    {z : Space} (t : ℝ)
    (hx : affinePath c d z t ∈ openEnlargement
      (lowerEndpoint a c d t) (lowerEndpoint b c d t) η) :
    HasDerivAt (affinePath c d z)
      (movingBoxVelocity a b c d η t (affinePath c d z t)) t := by
  have hn (s : ℝ) (i : Fin 3) := (hp s i).ne'
  rw [movingBoxVelocity, localizedAffine_eq hη (logarithmicRate_trace_zero hd hn hdet t)
    hx]
  apply hasDerivAt_pi.mpr
  intro i
  have hci := (hasDerivAt_pi.mp ((hc.differentiable (by simp) t).hasDerivAt) i)
  have hdi := ((contDiff_pi.mp hd i).differentiable (by simp) t).hasDerivAt
  have he : deriv c t i + logarithmicRate d t i * (affinePath c d z t i - c t i) =
      deriv c t i + deriv (fun s => d s i) t * z i := by
    dsimp [logarithmicRate, affinePath]
    field_simp [hn t i]
    ring
  rw [he]
  exact hci.fun_add (hdi.mul_const (z i))

theorem affinePath_hasDerivAt {a b : Space} {c d : ℝ → Space} {η : ℝ}
    (hη : 0 < η) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hp : ∀ t i, 0 < d t i) (hdet : ∀ t, ∏ i, d t i = 1)
    {z : Space} (hz : z ∈ Set.Icc a b) (t : ℝ) :
    HasDerivAt (affinePath c d z)
      (movingBoxVelocity a b c d η t (affinePath c d z t)) t :=
  affinePath_hasDerivAt_of_mem_plateau hη hc hd hp hdet t
    (affinePath_mem_plateau hη hz (hp t))

lemma affinePath_mem_plateau_of_scaled_bound {a b : Space} {c d : ℝ → Space}
    {η δ : ℝ} {z : Space} (hz : z ∈ openEnlargement a b δ) {t : ℝ}
    (hp : ∀ i, 0 < d t i) (hscale : ∀ i, d t i * δ ≤ η) :
    affinePath c d z t ∈ openEnlargement (lowerEndpoint a c d t)
      (lowerEndpoint b c d t) η := by
  rw [mem_openEnlargement] at hz ⊢
  intro i
  have hlo := mul_lt_mul_of_pos_left (hz i).1 (hp i)
  have hhi := mul_lt_mul_of_pos_left (hz i).2 (hp i)
  dsimp [affinePath, lowerEndpoint]
  constructor <;> nlinarith [hscale i]

theorem affinePath_neighborhood {a b : Space} {c d : ℝ → Space} {η δ : ℝ}
    (hη : 0 < η) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hp : ∀ t i, 0 < d t i) (hdet : ∀ t, ∏ i, d t i = 1)
    {z : Space} (hz : z ∈ openEnlargement a b δ) (t : ℝ)
    (hscale : ∀ i, d t i * δ ≤ η) :
    HasDerivAt (affinePath c d z)
      (movingBoxVelocity a b c d η t (affinePath c d z t)) t :=
  affinePath_hasDerivAt_of_mem_plateau hη hc hd hp hdet t
    (affinePath_mem_plateau_of_scaled_bound hz (hp t) hscale)

@[simp] lemma affinePotential_zero (c : Space) : affinePotential c 0 0 = 0 := by
  ext x i
  fin_cases i <;> simp [affinePotential]

@[simp] lemma localizedAffine_zero (a b c : Space) (η : ℝ) :
    localizedAffine a b c 0 0 η = 0 := by
  unfold localizedAffine
  have he : (fun x => boxCutoff a b η x • affinePotential c 0 0 x) = 0 := by
    ext x i
    fin_cases i <;> simp [affinePotential]
  rw [he]
  exact curl_zero

theorem movingBoxVelocity_zero {a b : Space} {c d : ℝ → Space} {η t : ℝ}
    (hc : deriv c t = 0) (hd : ∀ i, deriv (fun s => d s i) t = 0) :
    movingBoxVelocity a b c d η t = 0 := by
  have hl : logarithmicRate d t = 0 := by ext i; simp [logarithmicRate, hd]
  simp [movingBoxVelocity, hc, hl]

lemma tsupport_movingBoxVelocity_subset (a b : Space) (c d : ℝ → Space) {η : ℝ}
    (hη : 0 < η) (t : ℝ) :
    tsupport (movingBoxVelocity a b c d η t) ⊆
      closedEnlargement (lowerEndpoint a c d t) (lowerEndpoint b c d t) (2 * η) :=
  tsupport_localizedAffine_subset _ _ _ _ _ hη

end BalancedTransport.Geometry
end

end OAI
