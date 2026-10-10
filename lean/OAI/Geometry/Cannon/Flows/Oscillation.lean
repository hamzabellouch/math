import Mathlib
import OAI.Geometry.Cannon.Modulus.AnnularPatternDistance

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
namespace CannonNode

open Set Metric CannonMagnification

theorem good_candidate_pattern {X : Type*} [MetricSpace X] [ProperSpace X]
    {ι : Type*} [Fintype ι] (net : ι → X) (f : X → ℝ) (Ω : Set X)
    (h : X ≃ₜ X) (x : X) (y : Bool → X)
    (R θ A B c₀ cIn cPat CE LE gap δ : ℝ)
    (hR : 0 < R) (hθ : 0 < θ) (hA : 2 < A) (hB : 1 ≤ B)
    (hc₀ : 0 < c₀) (_hcIn : 0 < cIn) (hcPat : 0 < cPat)
    (hCE : 0 ≤ CE) (hLE : 0 ≤ LE) (hsmall : c₀*θ ≤ 1)
    (hinner : cIn ≤ c₀) (hinner2 : 2 ≤ c₀)
    (hcoef₁ : CE*cIn ≤ (cPat/2)*(A-2)^2)
    (hcoef₂ : LE*(10*cPat)*B*(B+1) < c₀)
    (hexp : Expansion h x R CE LE)
    (hloc : ∀ s, (A-1)*R ≤ dist x (y s) ∧ dist x (y s) ≤ B*R)
    (hΩ : ∀ s, closedBall (y s) (c₀*θ*R) ⊆ Ω)
    (hf : ContinuousOn f Ω)
    (hnet : ∀ z, ∃ i, dist z (net i) ≤ cPat*θ)
    (hpaths : ∀ s u v, u ∈ closedBall (y s) (2*θ*R) →
      v ∈ closedBall (y s) (2*θ*R) →
      JoinedIn (ball (y s) (cIn*θ*R)) u v)
    (hgap : ∀ s, gap ≤ upper f (y s) (2*θ*R)-lower f (y s) (2*θ*R))
    (hsep : upper f (y false) (c₀*θ*R)+δ ≤ lower f (y true) (c₀*θ*R)) :
    ∃ pat : Bool → ι, ∃ v₀ v₁ : Bool → X, ∃ γ : ∀ s, Path (v₀ s) (v₁ s),
      (∀ s, range (γ s) ⊆ closedBall (net (pat s)) (3*cPat*θ)) ∧
      (∀ s, gap ≤ f (h.symm (v₁ s))-f (h.symm (v₀ s))) ∧
      (∀ s, closedBall (net (pat s)) (3*cPat*θ) ⊆ h '' ball (y s) (c₀*θ*R)) ∧
      ∀ z ∈ closedBall (net (pat false)) (3*cPat*θ),
        ∀ w ∈ closedBall (net (pat true)) (3*cPat*θ),
          f (h.symm z)+δ ≤ f (h.symm w) := by
  classical
  have hr : 0 < θ*R := mul_pos hθ hR
  have hinnerball (s : Bool) : closedBall (y s) (2*θ*R) ⊆ closedBall (y s) (c₀*θ*R) :=
    closedBall_subset_closedBall (by nlinarith only [hinner2,hr])
  have hfc (s : Bool) := hf.mono (hΩ s)
  have hext (s : Bool) := ball_extrema (by positivity : 0 ≤ 2*θ*R) ((hfc s).mono (hinnerball s))
  choose v hv hvval using fun s => (hext s).1
  choose w hw hwval using fun s => (hext s).2
  have hp (s : Bool) := hpaths s (v s) (w s) (hv s) (hw s)
  choose π hπ using hp
  choose idx hidx using fun s => hnet (h (y s))
  let γ : ∀ s, Path (h (v s)) (h (w s)) := fun s => (π s).map h.continuous
  have hsmall' : cIn*θ ≤ 1 := (mul_le_mul_of_nonneg_right hinner hθ.le).trans hsmall
  have himage (s : Bool) : range (γ s) ⊆ closedBall (h (y s)) (cPat*θ/2) := by
    rintro z ⟨t,rfl⟩
    have hyt : dist (y s) (π s t) ≤ cIn*θ*R := by
      have hh := hπ s t
      change dist (π s t) (y s) < cIn*θ*R at hh
      simpa only [dist_comm] using hh.le
    have hyt' := dist_triangle x (π s t) (y s)
    rw [dist_comm (π s t) (y s)] at hyt'
    have hlow : (A-2)*R ≤ dist x (π s t) := by
      have hm := mul_le_mul_of_nonneg_right hsmall' hR.le
      nlinarith only [(hloc s).1,hyt,hyt',hm]
    have hh := annular_pattern_distance h x (y s) (π s t) R θ CE LE (A-2) cIn (cPat/2)
      hR hθ.le (by linarith only [hA]) hCE hexp
      (by nlinarith only [(hloc s).1,hR]) hlow hyt hcoef₁
    change dist (h (π s t)) (h (y s)) ≤ cPat*θ/2
    rw [dist_comm]
    nlinarith only [hh]
  have hcont (s : Bool) : closedBall (h (y s)) (10*(cPat*θ)) ⊆ h '' ball (y s) (c₀*θ*R) := by
    simpa only [mul_assoc] using pattern_ball_containment h x (y s) R θ CE LE B c₀ (10*cPat)
      hR hθ hLE hB hc₀ (by positivity) hsmall hexp (hloc s).2 hcoef₂
  have hb (s : Bool) := net_pattern_ball (h (y s)) (net (idx s)) (cPat*θ)
    (mul_nonneg hcPat.le hθ.le) (hidx s)
  refine ⟨idx,fun s => h (v s),fun s => h (w s),γ,?_,?_,?_,?_⟩
  · intro s
    simpa only [mul_assoc] using (himage s).trans (hb s).1
  · intro s
    simp only [h.symm_apply_apply]
    rw [hvval s,hwval s]
    exact hgap s
  · intro s
    simpa only [mul_assoc] using (hb s).2.trans (hcont s)
  · intro z hz w hw'
    have hz' : h.symm z ∈ closedBall (y false) (c₀*θ*R) := by
      have hh := (hb false).2 (by simpa only [mul_assoc] using hz)
      obtain ⟨v,hv,hvz⟩ := hcont false hh
      rw [← hvz,h.symm_apply_apply]
      exact ball_subset_closedBall hv
    have hw' : h.symm w ∈ closedBall (y true) (c₀*θ*R) := by
      have hh := (hb true).2 (by simpa only [mul_assoc] using hw')
      obtain ⟨v,hv,hvw⟩ := hcont true hh
      rw [← hvw,h.symm_apply_apply]
      exact ball_subset_closedBall hv
    linarith only [(ball_range (hfc false) hz').2,hsep,(ball_range (hfc true) hw').1]

end CannonNode

end

namespace CannonNode

open Set Metric CannonCapacity CannonMagnification

lemma clip_difference_le {a b l u : ℝ} (hab : a ≤ b) (hlu : l ≤ u) :
    clip a b u-clip a b l ≤ u-l := by
  rw [clip_difference hab hlu]
  apply max_le (sub_nonneg.mpr hlu)
  linarith only [min_le_right b u, le_max_right a l]

namespace SourceConstruction

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] [ProperSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

theorem node_pattern {ι : Type*} [Fintype ι] (net : ι → X)
    (Ω : Set X) (hf : ContinuousOn f Ω) (hloc : closedBall x₀ (2*ε) ⊆ Ω)
    (L CE LE cPat : ℝ) (hL : 1 ≤ L) (hCE : 0 ≤ CE) (hLE : 0 ≤ LE)
    (hcPat : 0 < cPat) (hA : 2 < A) (hB : 0 ≤ B) (hc₀ : 2*L ≤ c₀)
    (hcoef₁ : CE*(2*L) ≤ (cPat/2)*(A-2)^2)
    (hcoef₂ : LE*(10*cPat)*(B+1)*(B+2) < c₀)
    (hsmall : (B+2)*ρ ≤ ε)
    (hnet : ∀ z, ∃ i, dist z (net i) ≤ cPat*radius ell (160*(qdim+1)*n))
    (hpaths : ∀ x u w : X, ∀ r : ℝ, 0 < r → dist u x ≤ r → dist w x ≤ r →
      JoinedIn (ball x (L*r)) u w)
    (v : SourceNode f x₀ ε ell c₀ (B+1) S.kmin) (hv : S.good v)
    (h : X ≃ₜ X) (hexp : Expansion h v.center (radius ell v.depth) CE LE) :
    ∃ pat : Bool → ι, ∃ v₀ v₁ : Bool → X, ∃ γ : ∀ s, Path (v₀ s) (v₁ s),
      (∀ s, range (γ s) ⊆ closedBall (net (pat s)) (3*cPat*radius ell (160*(qdim+1)*n))) ∧
      (∀ s, S.κ*v.length ≤ f (h.symm (v₁ s))-f (h.symm (v₀ s))) ∧
      (∀ s, ∃ y ∈ S.Y v,
        closedBall (net (pat s)) (3*cPat*radius ell (160*(qdim+1)*n)) ⊆
          h '' ball y (c₀*radius ell (v.depth+160*(qdim+1)*n))) ∧
      ∀ z ∈ closedBall (net (pat false)) (3*cPat*radius ell (160*(qdim+1)*n)),
        ∀ w ∈ closedBall (net (pat true)) (3*cPat*radius ell (160*(qdim+1)*n)),
          f (h.symm z)+v.length/4 ≤ f (h.symm w) := by
  classical
  let θ := radius ell (160*(qdim+1)*n)
  let R := radius ell v.depth
  have hθ : 0 < θ := radius_pos _ _
  have hR : 0 < R := radius_pos _ _
  have hc₂ : 2 ≤ c₀ := (by linarith only [hL] : 2 ≤ 2*L).trans hc₀
  have hc : 0 < c₀ := by linarith only [hc₂]
  have hB' : 0 ≤ B+1 := by linarith only [hB]
  have hθsmall : c₀*θ ≤ 1 := S.pattern_small
  have hgeom (y : S.Y v) : (A-1)*R ≤ dist v.center y ∧ dist v.center y ≤ (B+1)*R := by
    simpa only [dist_comm] using S.Yloc v y y.property
  have hyΩ (y : S.Y v) : closedBall (y:X) (c₀*θ*R) ⊆ Ω := by
    intro z hz
    apply hloc
    rw [mem_closedBall] at hz ⊢
    have ht := dist_triangle z y v.center
    have ht' := dist_triangle z v.center x₀
    have hy := (S.Yloc v y y.property).2
    have hx := mem_closedBall.mp (v.center_mem hB')
    have hsm := mul_le_mul_of_nonneg_right hθsmall hR.le
    have hrho := mul_le_mul_of_nonneg_left (S.small v.depth v.lowerDepth)
      (by linarith only [hB] : 0 ≤ B+2)
    change (B+2)*R ≤ (B+2)*ρ at hrho
    linarith only [hz,ht,ht',hy,hx,hsm,hrho,hsmall]
  have hinner (y : S.Y v) : lower f (y:X) (2*θ*R) ≤ upper f y (2*θ*R) :=
    lower_le_upper (by positivity) ((hf.mono (hyΩ y)).mono
      (closedBall_subset_closedBall (by nlinarith only [hc₂,mul_pos hθ hR])))
  obtain ⟨i,j,hgi,hgj,hsep⟩ := hv
  simp only [radius_add] at hgi hgj hsep
  have hgi' : S.κ*v.length ≤ upper f (i:X) (2*θ*R)-lower f i (2*θ*R) := by
    apply hgi.trans
    simpa only [θ, R, mul_assoc] using clip_difference_le
      (show v.a ≤ v.a+(v.b-v.a)/4 by linarith only [v.ab]) (hinner i)
  have hgj' : S.κ*v.length ≤ upper f (j:X) (2*θ*R)-lower f j (2*θ*R) := by
    apply hgj.trans
    simpa only [θ, R, mul_assoc] using clip_difference_le
      (show v.a+3*(v.b-v.a)/4 ≤ v.b by linarith only [v.ab]) (hinner j)
  let y : Bool → X := fun s => if s then j else i
  have hy (s : Bool) : y s ∈ S.Y v := by cases s <;> exact Subtype.property _
  have hyloc (s : Bool) : (A-1)*R ≤ dist v.center (y s) ∧ dist v.center (y s) ≤ (B+1)*R := by
    cases s <;> exact hgeom _
  have hgap (s : Bool) : S.κ*v.length ≤ upper f (y s) (2*θ*R)-lower f (y s) (2*θ*R) := by
    cases s
    · exact hgi'
    · exact hgj'
  have hsep' : upper f (y false) (c₀*θ*R)+v.length/4 ≤ lower f (y true) (c₀*θ*R) := by
    simpa only [θ, R, y, Bool.false_eq_true, ↓reduceIte, SourceNode.length, mul_assoc] using hsep
  obtain ⟨pat,v₀,v₁,γ,hγ,hvar,hball,hrange⟩ := good_candidate_pattern net f Ω h v.center y
    R θ A (B+1) c₀ (2*L) cPat CE LE (S.κ*v.length) (v.length/4) hR hθ hA
    (by linarith only [hB]) hc (by linarith only [hL]) hcPat hCE hLE hθsmall
    hc₀ hc₂ hcoef₁ (by convert hcoef₂ using 1; ring) hexp hyloc
    (fun s => by cases s <;> exact hyΩ _) hf hnet
    (fun s u w hu hw => by
      simpa only [mul_assoc, mul_left_comm L 2] using
        hpaths (y s) u w (2*θ*R) (by positivity) (mem_closedBall.mp hu) (mem_closedBall.mp hw))
    hgap hsep'
  refine ⟨pat,v₀,v₁,γ,hγ,hvar,?_,hrange⟩
  intro s
  refine ⟨y s,hy s,?_⟩
  simpa only [θ, R, radius_add,mul_assoc] using hball s

end SourceConstruction

end CannonNode

end

section

namespace CannonNode

theorem exists_flow_constants {Lp CE LE Cμ : ℝ}
    (hLp : 1 ≤ Lp) (hCE : 0 < CE) (hLE : 0 < LE) (_hCμ : 0 ≤ Cμ) :
    ∃ c₀ A B₀ cPat H : ℝ,
      2*Lp+2 < c₀ ∧ A=4*Lp*c₀+20 ∧ B₀=A+10 ∧
      cPat=2*CE*(2*Lp)/(A-2)^2 ∧ 0 < cPat ∧
      12*cPat*(B₀+2)^2*LE < c₀ ∧
      max (4*(B₀+1)) (max (4*Cμ*c₀) 2) < H := by
  let cIn := 2*Lp
  have hcin : 2 ≤ cIn := by dsimp [cIn]; linarith only [hLp]
  let c₀ := 100*CE*LE*cIn+cIn+3
  have hc₀ : cIn+2 < c₀ := by
    dsimp [c₀]
    have hh : 0 < CE*LE*cIn := by positivity
    nlinarith only [hh]
  have hc₀pos : 0 < c₀ := by linarith only [hc₀,hcin]
  let A := 4*Lp*c₀+20
  have hA : 20 < A := by
    have hh : 0 < 4*Lp*c₀ := by positivity
    dsimp [A]
    linarith only [hh]
  let B₀ := A+10
  let cPat := 2*CE*cIn/(A-2)^2
  have hd : 0 < (A-2)^2 := sq_pos_of_pos (by linarith only [hA])
  have hratio : (B₀+2)^2 ≤ 4*(A-2)^2 := by
    have hh : 0 ≤ A-2 := by linarith only [hA]
    have hh' : 0 ≤ B₀+2 := by dsimp [B₀]; linarith only [hA]
    have hu : B₀+2 ≤ 2*(A-2) := by dsimp [B₀]; linarith only [hA]
    have hz := pow_le_pow_left₀ hh' hu 2
    nlinarith only [hz]
  have hmargin : 12*cPat*(B₀+2)^2*LE < c₀ := by
    have hco : 0 < 24*CE*cIn*LE := by positivity
    have hmul := mul_le_mul_of_nonneg_left hratio hco.le
    have hc : 96*CE*cIn*LE < c₀ := by
      dsimp [c₀]
      have hh : 0 < CE*LE*cIn := by positivity
      nlinarith only [hh,hcin]
    have hc' := mul_lt_mul_of_pos_right hc hd
    have heq : 12*cPat*(B₀+2)^2*LE = (24*CE*cIn*LE*(B₀+2)^2)/(A-2)^2 := by
      dsimp [cPat]
      ring
    rw [heq]
    apply (div_lt_iff₀ hd).mpr
    nlinarith only [hmul,hc']
  refine ⟨c₀,A,B₀,cPat,max (4*(B₀+1)) (max (4*Cμ*c₀) 2)+1,
    hc₀,rfl,rfl,rfl,div_pos (by positivity) hd,hmargin,?_⟩
  linarith

end CannonNode

end

section

open Set MeasureTheory
open scoped BigOperators

namespace CannonCrossEnergy

theorem weighted_interval_cover {ι : Type*} [Fintype ι]
    (L U w : ι → ℝ) (a b c : ℝ) (hab : a ≤ b)
    (hLU : ∀ i, L i ≤ U i) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ t ∈ Icc a b,
      c ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => w i) t) :
    c * (b - a) ≤ ∑ i, w i * (U i - L i) := by
  have hint (l u v : ℝ) : Integrable ((Icc l u).indicator (fun _ : ℝ => v)) := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hle : (Icc a b).indicator (fun _ : ℝ => c) ≤
      fun t => ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => w i) t := by
    intro t
    by_cases ht : t ∈ Icc a b
    · simpa [Set.indicator_of_mem ht] using hcover t ht
    · rw [Set.indicator_of_notMem ht]
      exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => hw i) _)
  have hi := integral_mono (hint a b c)
    (integrable_finsetSum _ (fun i _ => hint (L i) (U i) (w i))) hle
  rw [integral_finsetSum _ (fun i _ => hint (L i) (U i) (w i))] at hi
  simpa only [integral_indicator_const _ measurableSet_Icc, Measure.real,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hLU _)), smul_eq_mul, mul_comm] using hi

end CannonCrossEnergy

namespace CannonCrossEnergy

variable {X : Type*} [TopologicalSpace X]

def oscillation (f : X → ℝ) (A : Set X) : ℝ :=
  sSup (f '' A) - sInf (f '' A)

def rangeInterval (f : X → ℝ) (A : Set X) : Set ℝ :=
  Icc (sInf (f '' A)) (sSup (f '' A))

lemma mem_rangeInterval {f : X → ℝ} {A : Set X} (hf : Continuous f)
    (hA : IsCompact A) {x : X} (hx : x ∈ A) : f x ∈ rangeInterval f A := by
  have hc := hA.image hf
  exact ⟨csInf_le hc.bddBelow (mem_image_of_mem f hx),
    le_csSup hc.bddAbove (mem_image_of_mem f hx)⟩

lemma oscillation_nonneg {f : X → ℝ} {A : Set X} (hf : Continuous f)
    (hA : IsCompact A) (hne : A.Nonempty) : 0 ≤ oscillation f A := by
  exact sub_nonneg.mpr (csInf_le_csSup (hne.image f)
    (hA.image hf).bddBelow (hA.image hf).bddAbove)

lemma rangeInterval_eq_image {f : X → ℝ} {A : Set X} (hf : Continuous f)
    (hA : IsCompact A) (hne : A.Nonempty) (hcon : IsPreconnected A) :
    rangeInterval f A = f '' A := by
  apply le_antisymm
  · exact (hcon.image f hf.continuousOn).ordConnected.out
      ((hA.image hf).sInf_mem (hne.image f)) ((hA.image hf).sSup_mem (hne.image f))
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_rangeInterval hf hA hx

theorem level_continuum_cover {ι : Type*} [Fintype ι]
    (C : ι → Set X) (hC : ∀ i, IsCompact (C i))
    (hne : ∀ i, (C i).Nonempty) (f w : X → ℝ)
    (hf : Continuous f) (hw : Continuous w) (D : Set X)
    (hD : IsCompact D) (hDne : D.Nonempty) (hDcon : IsPreconnected D)
    (hcover : ∀ x ∈ D, ∃ i, x ∈ C i) (t : ℝ) (hlevel : ∀ x ∈ D, f x = t) :
    oscillation w D ≤ ∑ i, (rangeInterval f (C i)).indicator
      (fun _ : ℝ => oscillation w (C i)) t := by
  classical
  let weights : ι → ℝ := fun i => if t ∈ rangeInterval f (C i) then 1 else 0
  have hweights : ∀ i, 0 ≤ weights i := by
    intro i
    dsimp [weights]
    split_ifs <;> norm_num
  have hrange : ∀ v ∈ rangeInterval w D,
      1 ≤ ∑ i, (rangeInterval w (C i)).indicator (fun _ : ℝ => weights i) v := by
    intro v hv
    rw [rangeInterval_eq_image hw hD hDne hDcon] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨i, hi⟩ := hcover x hx
    have hti : t ∈ rangeInterval f (C i) := by
      rw [← hlevel x hx]
      exact mem_rangeInterval hf (hC i) hi
    have hwi : w x ∈ rangeInterval w (C i) := mem_rangeInterval hw (hC i) hi
    calc
      1 = (rangeInterval w (C i)).indicator (fun _ : ℝ => weights i) (w x) := by
        simp [Set.indicator_of_mem hwi, weights, hti]
      _ ≤ ∑ j, (rangeInterval w (C j)).indicator (fun _ : ℝ => weights j) (w x) :=
        Finset.single_le_sum (f := fun j => (rangeInterval w (C j)).indicator
          (fun _ : ℝ => weights j) (w x)) (fun j _ => Set.indicator_nonneg
          (fun _ _ => hweights j) (w x)) (Finset.mem_univ i)
  have h := weighted_interval_cover
    (fun i => sInf (w '' C i)) (fun i => sSup (w '' C i)) weights
    (sInf (w '' D)) (sSup (w '' D)) 1
    (sub_nonneg.mp (oscillation_nonneg hw hD hDne))
    (fun i => sub_nonneg.mp (oscillation_nonneg hw (hC i) (hne i)))
    hweights hrange
  simp only [one_mul] at h
  change oscillation w D ≤ _ at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : t ∈ rangeInterval f (C i)
  · simp [weights, ht, oscillation]
  · simp [weights, ht]

theorem finite_cell_level_comparison {ι : Type*} [Fintype ι]
    (C : ι → Set X) (hC : ∀ i, IsCompact (C i))
    (hne : ∀ i, (C i).Nonempty) (K : Set X)
    (hcover : ∀ x ∈ K, ∃ i, x ∈ C i)
    (f w : X → ℝ) (hf : Continuous f) (hw : Continuous w)
    (a b b₀ : ℝ) (hab : a ≤ b)
    (hlevels : ∀ t ∈ Icc a b, ∃ D : Set X,
      IsCompact D ∧ D.Nonempty ∧ IsPreconnected D ∧ D ⊆ K ∧
      (∀ x ∈ D, f x = t) ∧ b₀ ≤ oscillation w D) :
    b₀ * (b - a) ≤ ∑ i, oscillation f (C i) * oscillation w (C i) := by
  have hpoint : ∀ t ∈ Icc a b,
      b₀ ≤ ∑ i, (rangeInterval f (C i)).indicator
        (fun _ : ℝ => oscillation w (C i)) t := by
    intro t ht
    obtain ⟨D, hD, hDne, hDcon, hDK, hlevel, hwD⟩ := hlevels t ht
    exact hwD.trans (level_continuum_cover C hC hne f w hf hw D hD hDne hDcon
      (fun x hx => hcover x (hDK hx)) t hlevel)
  have h := weighted_interval_cover
    (fun i => sInf (f '' C i)) (fun i => sSup (f '' C i))
    (fun i => oscillation w (C i)) a b b₀ hab
    (fun i => sub_nonneg.mp (oscillation_nonneg hf (hC i) (hne i)))
    (fun i => oscillation_nonneg hw (hC i) (hne i)) hpoint
  simpa only [oscillation, mul_comm] using h

end CannonCrossEnergy

namespace CannonCrossEnergy

open Filter Topology

theorem no_vanishing_cross_energy {X : Type*} [TopologicalSpace X]
    (I : ℕ → Type*) [∀ n, Fintype (I n)]
    (C : ∀ n, I n → Set X) (hC : ∀ n i, IsCompact (C n i))
    (hCn : ∀ n i, (C n i).Nonempty) (K : Set X)
    (hcover : ∀ n x, x ∈ K → ∃ i, x ∈ C n i)
    (f w : ℕ → X → ℝ) (hf : ∀ n, Continuous (f n)) (hw : ∀ n, Continuous (w n))
    (a b q : ℝ) (hab : a < b) (hq : 0 < q)
    (hlevels : ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∃ D : Set X,
      IsCompact D ∧ D.Nonempty ∧ IsPreconnected D ∧ D ⊆ K ∧
      (∀ x ∈ D, f n x = t) ∧ q ≤ oscillation (w n) D)
    (hfe : Tendsto (fun n => ∑ i, (oscillation (f n) (C n i))^2) atTop (𝓝 0))
    (hwe : Tendsto (fun n => ∑ i, (oscillation (w n) (C n i))^2) atTop (𝓝 0)) :
    False := by
  have he := hfe.mul hwe
  simp only [mul_zero] at he
  have hlow : (q*(b-a))^2 ≤ (0:ℝ) := by
    apply ge_of_tendsto he
    filter_upwards [hlevels] with n hn
    have hsum := finite_cell_level_comparison (C n) (hC n) (hCn n) K
      (hcover n) (f n) (w n) (hf n) (hw n) a b q hab.le hn
    calc
      (q*(b-a))^2 ≤ (∑ i, oscillation (f n) (C n i)*oscillation (w n) (C n i))^2 :=
        pow_le_pow_left₀ (mul_nonneg hq.le (sub_nonneg.mpr hab.le)) hsum 2
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  exact (not_le_of_gt (sq_pos_of_pos (mul_pos hq (sub_pos.mpr hab)))) hlow

end CannonCrossEnergy

namespace CannonCrossEnergyLocal

variable {X : Type*} [TopologicalSpace X]

open CannonCrossEnergy

lemma mem_rangeInterval {f : X → ℝ} {A : Set X} (hf : ContinuousOn f A)
    (hA : IsCompact A) {x : X} (hx : x ∈ A) : f x ∈ rangeInterval f A := by
  have hc := hA.image_of_continuousOn hf
  exact ⟨csInf_le hc.bddBelow (mem_image_of_mem f hx),
    le_csSup hc.bddAbove (mem_image_of_mem f hx)⟩

lemma oscillation_nonneg {f : X → ℝ} {A : Set X} (hf : ContinuousOn f A)
    (hA : IsCompact A) (hne : A.Nonempty) : 0 ≤ oscillation f A := by
  exact sub_nonneg.mpr (csInf_le_csSup (hne.image f)
    (hA.image_of_continuousOn hf).bddBelow (hA.image_of_continuousOn hf).bddAbove)

lemma rangeInterval_eq_image {f : X → ℝ} {A : Set X} (hf : ContinuousOn f A)
    (hA : IsCompact A) (hne : A.Nonempty) (hcon : IsPreconnected A) :
    rangeInterval f A = f '' A := by
  apply le_antisymm
  · exact (hcon.image f hf).ordConnected.out
      ((hA.image_of_continuousOn hf).sInf_mem (hne.image f)) ((hA.image_of_continuousOn hf).sSup_mem (hne.image f))
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_rangeInterval hf hA hx

theorem level_continuum_cover {ι : Type*} [Fintype ι]
    (C : ι → Set X) (hC : ∀ i, IsCompact (C i))
    (hne : ∀ i, (C i).Nonempty) (f w : X → ℝ)
    (S : Set X) (hCS : ∀ i, C i ⊆ S)
    (hf : ContinuousOn f S) (hw : ContinuousOn w S) (D : Set X) (hDS : D ⊆ S)
    (hD : IsCompact D) (hDne : D.Nonempty) (hDcon : IsPreconnected D)
    (hcover : ∀ x ∈ D, ∃ i, x ∈ C i) (t : ℝ) (hlevel : ∀ x ∈ D, f x = t) :
    oscillation w D ≤ ∑ i, (rangeInterval f (C i)).indicator
      (fun _ : ℝ => oscillation w (C i)) t := by
  classical
  let weights : ι → ℝ := fun i => if t ∈ rangeInterval f (C i) then 1 else 0
  have hweights : ∀ i, 0 ≤ weights i := by
    intro i
    dsimp [weights]
    split_ifs <;> norm_num
  have hrange : ∀ v ∈ rangeInterval w D,
      1 ≤ ∑ i, (rangeInterval w (C i)).indicator (fun _ : ℝ => weights i) v := by
    intro v hv
    rw [rangeInterval_eq_image (hw.mono hDS) hD hDne hDcon] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨i, hi⟩ := hcover x hx
    have hti : t ∈ rangeInterval f (C i) := by
      rw [← hlevel x hx]
      exact mem_rangeInterval (hf.mono (hCS i)) (hC i) hi
    have hwi : w x ∈ rangeInterval w (C i) := mem_rangeInterval (hw.mono (hCS i)) (hC i) hi
    calc
      1 = (rangeInterval w (C i)).indicator (fun _ : ℝ => weights i) (w x) := by
        simp [Set.indicator_of_mem hwi, weights, hti]
      _ ≤ ∑ j, (rangeInterval w (C j)).indicator (fun _ : ℝ => weights j) (w x) :=
        Finset.single_le_sum (f := fun j => (rangeInterval w (C j)).indicator
          (fun _ : ℝ => weights j) (w x)) (fun j _ => Set.indicator_nonneg
          (fun _ _ => hweights j) (w x)) (Finset.mem_univ i)
  have h := weighted_interval_cover
    (fun i => sInf (w '' C i)) (fun i => sSup (w '' C i)) weights
    (sInf (w '' D)) (sSup (w '' D)) 1
    (sub_nonneg.mp (oscillation_nonneg (hw.mono hDS) hD hDne))
    (fun i => sub_nonneg.mp (oscillation_nonneg (hw.mono (hCS i)) (hC i) (hne i)))
    hweights hrange
  simp only [one_mul] at h
  change oscillation w D ≤ _ at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : t ∈ rangeInterval f (C i)
  · simp [weights, ht, CannonCrossEnergy.oscillation]
  · simp [weights, ht]

theorem finite_cell_level_comparison {ι : Type*} [Fintype ι]
    (C : ι → Set X) (hC : ∀ i, IsCompact (C i))
    (hne : ∀ i, (C i).Nonempty) (K : Set X)
    (hcover : ∀ x ∈ K, ∃ i, x ∈ C i)
    (f w : X → ℝ) (S : Set X) (hKS : K ⊆ S) (hCS : ∀ i, C i ⊆ S)
    (hf : ContinuousOn f S) (hw : ContinuousOn w S)
    (a b b₀ : ℝ) (hab : a ≤ b)
    (hlevels : ∀ t ∈ Icc a b, ∃ D : Set X,
      IsCompact D ∧ D.Nonempty ∧ IsPreconnected D ∧ D ⊆ K ∧
      (∀ x ∈ D, f x = t) ∧ b₀ ≤ oscillation w D) :
    b₀ * (b - a) ≤ ∑ i, oscillation f (C i) * oscillation w (C i) := by
  have hpoint : ∀ t ∈ Icc a b,
      b₀ ≤ ∑ i, (rangeInterval f (C i)).indicator
        (fun _ : ℝ => oscillation w (C i)) t := by
    intro t ht
    obtain ⟨D, hD, hDne, hDcon, hDK, hlevel, hwD⟩ := hlevels t ht
    exact hwD.trans (level_continuum_cover C hC hne f w S hCS hf hw D (hDK.trans hKS) hD hDne hDcon
      (fun x hx => hcover x (hDK hx)) t hlevel)
  have h := weighted_interval_cover
    (fun i => sInf (f '' C i)) (fun i => sSup (f '' C i))
    (fun i => oscillation w (C i)) a b b₀ hab
    (fun i => sub_nonneg.mp (oscillation_nonneg (hf.mono (hCS i)) (hC i) (hne i)))
    (fun i => oscillation_nonneg (hw.mono (hCS i)) (hC i) (hne i)) hpoint
  simpa only [CannonCrossEnergy.oscillation, mul_comm] using h

end CannonCrossEnergyLocal

end
end
end
end
end
end
end
end

end OAI
