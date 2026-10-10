import OAI.Analysis.CStarAlgebra.PureInfiniteness.Compression

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
local instance shrinkingPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance shrinkingStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance shrinkingOperatorPartialOrder (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    PartialOrder (J →L[ℂ] J) := CStarAlgebra.spectralOrder _
local instance shrinkingOperatorStarOrderedRing (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] :
    StarOrderedRing (J →L[ℂ] J) := CStarAlgebra.spectralOrderedRing _

theorem conditional_shrinking {a y c p : A} (_ha : 0 ≤ a) (hy : 0 ≤ y)
    (hp : 0 ≤ p) (hpn : ‖p‖ ≤ 1) (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1)
    (hpH : p ∈ Her a)
    (hsignal : ∀ R : HilbertRep.{u,u} A, (1/2:ℝ)<‖R.hom a‖ → ‖R.hom p‖=1)
    (hvan : ∀ R : HilbertRep.{u,u} A,
      R.hom (y*(1-star c*(p*p)*c)*y)=0 → ‖R.hom y‖ ≤ (1/4:ℝ)) :
    ∃ (p₁ q₁ : A) (κ : ℝ), 0 ≤ p₁ ∧ ‖p₁‖ ≤ 1 ∧ p₁ ∈ Her a ∧
      0 ≤ q₁ ∧ ‖q₁‖ ≤ 1 ∧ q₁ ∈ Her y ∧ 0 ≤ κ ∧ κ < 1 ∧
      HerCompression p₁ q₁ c κ ∧
      (∀ R : HilbertRep.{u,u} A, (1/2:ℝ)<‖R.hom a‖ → ‖R.hom p₁‖=1) ∧
      (∀ R : HilbertRep.{u,u} A, (1/2:ℝ)<‖R.hom y‖ → ‖R.hom q₁‖=1) := by
  obtain ⟨δ,hδ,hδ₁,hquant⟩ := quantitative_nonvanishing hy hvan
  let d := y*(1-star c*(p*p)*c)*y
  have hd : 0 ≤ d := (conditional_defect_bounds hp hy hpn hyn hcn).1
  let q := y*cut d δ*y
  have hq : 0 ≤ q := by
    simpa only [hy.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg (cut_nonneg d δ) y
  have hqH : q ∈ Her y := by
    simpa only [hy.isSelfAdjoint.star_eq] using sandwich_mem_Her y (cut d δ)
  have hqvan (R : HilbertRep.{u,u} A) (hz : R.hom q=0) : ‖R.hom y‖ ≤ (3/8:ℝ) := by
    have hqzero : R.hom y * cut (R.hom y*(1-star (R.hom c)*(R.hom p*R.hom p)*R.hom c)*R.hom y) δ * R.hom y=0 := by
      change R.hom (y*cut d δ*y)=0 at hz
      rw [map_mul, map_mul, map_cut_sa R.hom hd.isSelfAdjoint hδ.le] at hz
      simpa only [d, map_mul, map_sub, map_one, map_star] using hz
    have hb := conditional_q_zero (map_nonneg R.hom hp) (map_nonneg R.hom hy)
      ((NonUnitalStarAlgHom.norm_apply_le R.hom p).trans hpn)
      ((NonUnitalStarAlgHom.norm_apply_le R.hom y).trans hyn)
      ((NonUnitalStarAlgHom.norm_apply_le R.hom c).trans hcn) hδ hqzero
    have hb' : ‖R.hom d‖ ≤ δ := by
      simpa only [d, map_mul, map_sub, map_one, map_star] using hb
    by_contra! hRy
    exact (not_lt_of_ge hb') (hquant R hRy)
  obtain ⟨δ',hδ',hδ'₁,hquant'⟩ := quantitative_nonvanishing_general hy
    (by norm_num : (0:ℝ)≤3/8) (by norm_num : (3/8:ℝ)<1/2) hqvan
  let r := Real.sqrt (1-δ)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr₁ : r < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr
    linarith
  let τ := (r+1)/2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hrτ : r < τ := by dsimp [τ]; linarith
  have hτ₁ : τ < 1 := by dsimp [τ]; linarith
  let p₁ := ramp p τ 1
  let q₁ := ramp q (δ'/2) δ'
  have hp₁ : 0 ≤ p₁ := ramp_nonneg p hτ₁.le
  have hq₁ : 0 ≤ q₁ := ramp_nonneg q (by linarith)
  have hq₁H : q₁ ∈ Her q :=
    Her_mono_of_mem (cut_mem_Her hq (δ'/2)) (ramp_mem_Her_cut hq (by positivity))
  refine ⟨p₁,q₁,r/τ,hp₁,norm_ramp_le_one p hτ₁.le,?_,hq₁,
    norm_ramp_le_one q (by linarith),Her_mono_of_mem hqH hq₁H,
    div_nonneg hr hτ.le,(div_lt_one hτ).mpr hrτ,?_,?_,?_⟩
  · exact Her_mono_of_mem hpH (Her_mono_of_mem (cut_mem_Her hp τ) (ramp_mem_Her_cut hp hτ.le))
  · have hcomp := compression_of_conditional_loss hp hτ hr (conditional_Her_loss hp hy hpn hyn hcn hδ.le hδ₁.le)
    intro x hx k hk
    exact hcomp x hx k (Her_mono_of_mem hq₁H hk)
  · intro R hRa
    change ‖R.hom (ramp p τ 1)‖=1
    rw [map_ramp_sa R.hom hp.isSelfAdjoint hτ.le]
    exact norm_ramp_eq_one (map_nonneg R.hom hp) hτ.le hτ₁ (by rw [hsignal R hRa])
  · intro R hRy
    change ‖R.hom (ramp q (δ'/2) δ')‖=1
    rw [map_ramp_sa R.hom hq.isSelfAdjoint (by positivity)]
    exact norm_ramp_eq_one (map_nonneg R.hom hq) (by positivity) (by linarith) (hquant' R hRy).le

theorem shrinking_unital_local {a y c : A} (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1)
    (hp : ∀ z : A, 0 ≤ z → z ∈ Her a → ProperlyInfinite z) :
    ∃ (p q : A) (κ : ℝ), 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her y ∧ 0 ≤ κ ∧ κ < 1 ∧
      HerCompression p q c κ ∧
      (∀ R : HilbertRep.{u,u} A, (1/2:ℝ)<‖R.hom a‖ → ‖R.hom p‖=1) ∧
      (∀ R : HilbertRep.{u,u} A, (1/2:ℝ)<‖R.hom y‖ → ‖R.hom q‖=1) := by
  obtain ⟨p,hpp,hpn,hpH,hsignal,hvan⟩ := graph_nonvanishing.{u,u} ha hy hcn hp
  exact conditional_shrinking ha hy hpp hpn hyn hcn hpH hsignal hvan

end MainGap

namespace MainGap
variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def matrixMap (π : A →⋆ₙₐ[ℂ] B) {m n : ℕ} (x : CStarMatrix (Fin m) (Fin n) A) :
    CStarMatrix (Fin m) (Fin n) B := CStarMatrix.ofMatrix (fun i j => π (x i j))

lemma matrixMap_mul (π : A →⋆ₙₐ[ℂ] B) {l m n : ℕ}
    (x : CStarMatrix (Fin l) (Fin m) A) (y : CStarMatrix (Fin m) (Fin n) A) :
    matrixMap π (x*y)=matrixMap π x * matrixMap π y := by
  ext i j
  change π (∑ k, x i k * y k j) = ∑ k, π (x i k) * π (y k j)
  simp only [map_sum, map_mul]

lemma matrixMap_star (π : A →⋆ₙₐ[ℂ] B) {m n : ℕ}
    (x : CStarMatrix (Fin m) (Fin n) A) :
    matrixMap π x.conjTranspose=(matrixMap π x).conjTranspose := by
  ext i j
  change π (star (x j i)) = star (π (x j i))
  exact map_star π _

lemma continuous_matrixMap (π : A →⋆ₙₐ[ℂ] B) {m n : ℕ} :
    Continuous (matrixMap π : CStarMatrix (Fin m) (Fin n) A → CStarMatrix (Fin m) (Fin n) B) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (map_continuous π).comp ((continuous_apply j).comp (continuous_apply i))

lemma FiniteCuntzLE.map (π : A →⋆ₙₐ[ℂ] B) {m n : ℕ}
    {d : CStarMatrix (Fin n) (Fin n) A} {v : CStarMatrix (Fin m) (Fin m) A}
    (h : FiniteCuntzLE d v) : FiniteCuntzLE (matrixMap π d) (matrixMap π v) := by
  obtain ⟨r,ht⟩ := h
  refine ⟨fun j => matrixMap π (r j), ?_⟩
  have he := (continuous_matrixMap π).continuousAt.tendsto.comp ht
  change Tendsto (fun j => matrixMap π ((r j).conjTranspose * v * r j)) atTop (𝓝 (matrixMap π d)) at he
  simpa only [matrixMap_mul, matrixMap_star] using he

lemma ProperlyInfinite.map (π : A →⋆ₙₐ[ℂ] B) {h : A} (hh : ProperlyInfinite h) :
    ProperlyInfinite (π h) := by
  have he := FiniteCuntzLE.map π hh
  have hdouble : matrixMap π (doubleCorner h)=doubleCorner (π h) := by
    ext i j
    change π (if i=j then h else 0) = if i=j then π h else 0
    split_ifs <;> simp
  have hsingle : matrixMap π (scalarCorner h)=scalarCorner (π h) := rfl
  change FiniteCuntzLE _ _
  rwa [hdouble, hsingle] at he

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance shrinkingHerPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance shrinkingHerStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance shrinkingHerUnitizationPartialOrder : PartialOrder (Unitization ℂ A) :=
  CStarAlgebra.spectralOrder _
local instance shrinkingHerUnitizationStarOrderedRing : StarOrderedRing (Unitization ℂ A) :=
  CStarAlgebra.spectralOrderedRing _

lemma unitization_Her {a : A} {z : Unitization ℂ A}
    (hz : z ∈ Her (a : Unitization ℂ A)) : z.fst=0 ∧ z.snd ∈ Her a := by
  have hc : IsClosed {z : Unitization ℂ A | z.fst=0 ∧ z.snd ∈ Her a} :=
    (isClosed_eq Unitization.continuous_fst continuous_const).inter
      ((isClosed_Her a).preimage Unitization.continuous_snd)
  apply closure_minimal (s := Set.range (fun b : Unitization ℂ A =>
    (a : Unitization ℂ A)*b*star (a : Unitization ℂ A))) _ hc hz
  rintro z ⟨b,rfl⟩
  constructor
  · simp
  · change ((a : Unitization ℂ A)*b*star (a : Unitization ℂ A)).snd ∈ Her a
    have he : ((a : Unitization ℂ A)*b*star (a : Unitization ℂ A)).snd =
        b.fst • (a*star a) + a*b.snd*star a := by
      simp [Unitization.snd_mul, Unitization.fst_mul, add_mul, smul_mul_assoc]
    rw [he]
    exact (Her a).add_mem ((Her a).smul_mem b.fst (mul_star_mem_Her a)) (sandwich_mem_Her a b.snd)

lemma unitization_inr_snd_of_Her {a : A} {z : Unitization ℂ A}
    (hz : z ∈ Her (a : Unitization ℂ A)) : (z.snd : Unitization ℂ A)=z := by
  have he := Unitization.inl_fst_add_inr_snd_eq z
  simpa only [(unitization_Her hz).1, Unitization.inl_zero, zero_add] using he

lemma unitization_proper_hereditary (hp : PropertyP A) {a : A}
    {z : Unitization ℂ A} (hz : 0 ≤ z) (hzH : z ∈ Her (a : Unitization ℂ A)) :
    ProperlyInfinite z := by
  have he := unitization_inr_snd_of_Her hzH
  have hz' : 0 ≤ z.snd := Unitization.inr_nonneg_iff.mp (he.symm ▸ hz)
  have hh := (hp z.snd hz').map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  change ProperlyInfinite (z.snd : Unitization ℂ A) at hh
  rwa [he] at hh

end MainGap

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
local instance shrinkingNonunitalPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance shrinkingNonunitalStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance shrinkingNonunitalUnitizationPartialOrder : PartialOrder (Unitization ℂ A) :=
  CStarAlgebra.spectralOrder _
local instance shrinkingNonunitalUnitizationStarOrderedRing : StarOrderedRing (Unitization ℂ A) :=
  CStarAlgebra.spectralOrderedRing _

def NormSignal (a p : A) : Prop :=
  ∀ R : HilbertRep.{u,u} (Unitization ℂ A), (1/2:ℝ)<‖R.hom (a : Unitization ℂ A)‖ →
    ‖R.hom (p : Unitization ℂ A)‖=1

theorem shrinking_nonunital (hp : PropertyP A) {a y c : A} (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1) :
    ∃ (p q : A) (κ : ℝ), 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her y ∧ 0 ≤ κ ∧ κ < 1 ∧
      HerCompression p q c κ ∧ NormSignal a p ∧ NormSignal y q := by
  obtain ⟨p,q,κ,hp0,hpn,hpH,hq0,hqn,hqH,hκ0,hκ1,hcomp,hps,hqs⟩ :=
    shrinking_unital_local (Unitization.inr_nonneg_iff.mpr ha)
      (Unitization.inr_nonneg_iff.mpr hy)
      (by simpa only [Unitization.norm_inr] using hyn : ‖(y : Unitization ℂ A)‖ ≤ 1)
      (by simpa only [Unitization.norm_inr] using hcn : ‖(c : Unitization ℂ A)‖ ≤ 1)
      (fun z hz hzH => unitization_proper_hereditary hp hz hzH)
  have hep := unitization_inr_snd_of_Her hpH
  have heq := unitization_inr_snd_of_Her hqH
  refine ⟨p.snd,q.snd,κ,Unitization.inr_nonneg_iff.mp (hep.symm ▸ hp0),?_,
    (unitization_Her hpH).2,Unitization.inr_nonneg_iff.mp (heq.symm ▸ hq0),?_,
    (unitization_Her hqH).2,hκ0,hκ1,?_,?_,?_⟩
  · have hn : ‖p.snd‖=‖p‖ := by simpa only [Unitization.norm_inr] using congrArg norm hep
    rwa [hn]
  · have hn : ‖q.snd‖=‖q‖ := by simpa only [Unitization.norm_inr] using congrArg norm heq
    rwa [hn]
  · intro x hx k hk
    have hx' := Her_map (Unitization.inrNonUnitalStarAlgHom ℂ A) hx
    have hk' := Her_map (Unitization.inrNonUnitalStarAlgHom ℂ A) hk
    change (x : Unitization ℂ A) ∈ Her (p.snd : Unitization ℂ A) at hx'
    change (k : Unitization ℂ A) ∈ Her (q.snd : Unitization ℂ A) at hk'
    rw [hep] at hx'
    rw [heq] at hk'
    have hb := hcomp _ hx' _ hk'
    simpa only [← Unitization.inr_mul, Unitization.norm_inr] using hb
  · intro R hRa
    rw [hep]
    exact hps R hRa
  · intro R hRy
    rw [heq]
    exact hqs R hRy
end MainGap

end

end OAI
