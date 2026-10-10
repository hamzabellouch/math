import Mathlib
import OAI.Geometry.BallPacking.BallMaps.SixCubicInnerNormalPacking

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial
open MomentPolytope

 theorem exists_cubic_bubble_separated {A B L S m p N k : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (hm : m+1<p) (t δ : ℝ) {c : ℝ} (hc : 0<c)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : 0<D 0) (hDL : (L:ℝ)*D 0=1)
     {r₀ : ℝ} (hr₀ : r₀<Real.pi*(D 0*((m+1:ℕ)*c)))
     (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient)
     (hf : ∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
       (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ) (f i))
     (hinto : ∀ i,∀ x∈closedBall 3 (r i),(f i x).2≠0)
     (hd : Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r i)) (f j '' closedBall 3 (r j))))
     {η : ℝ} (hη : 0<η) :
     ∃ ε∈Ioc (0:ℝ) η,∃ g₀ : Ambient 3 → Ambient 3,∃ g : Fin k → Ambient 3 → Ambient 3,
       FormNeighborhoodEmbedding (closedBall 3 r₀) (fun _ => successorStandardForm 2)
         (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)) g₀ ∧
       (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
         (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)) (g i)) ∧
       (∀ i,Disjoint (g₀ '' closedBall 3 r₀) (g i '' closedBall 3 (r i))) ∧
       Pairwise (fun i j => Disjoint (g i '' closedBall 3 (r i)) (g j '' closedBall 3 (r j))) := by
   let U : Set CubicAmbient := {z | z.2≠0}
   have hU : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
   have hgU : ContDiffOn ℝ ∞ firstToDistinguished U := fun _ hx =>
     (firstToDistinguished_smoothAt hx).contDiffWithinAt
   let K : Set CubicAmbient := ⋃ i,f i '' closedBall 3 (r i)
   have hK : IsCompact K := by
     apply isCompact_iUnion
     intro i
     obtain ⟨W,_hW,hKW,hs,_he,_hf⟩ := hf i
     exact (closedBall_isCompact 3 (r i)).image_of_continuousOn (hs.continuousOn.mono hKW)
   have hKU : K⊆U := by
     intro x hx
     obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
     exact hinto i y hy
   have hK' : IsCompact (firstToDistinguished '' K) :=
     hK.image_of_continuousOn (hgU.continuousOn.mono hKU)
   have hzero : (0 : Fin 3 → ℂ)∉firstToDistinguished '' K := by
     rintro ⟨x,hx,he⟩
     have he0 := congrFun he 0
     exact inv_ne_zero (hKU hx) he0
   obtain ⟨V,W,hV,hW,hKV,h0W,hVW⟩ :=
     normal_separation hK'.isClosed isClosed_singleton (disjoint_singleton_right.mpr hzero)
   let T : Set CubicAmbient := U ∩ firstToDistinguished ⁻¹' V
   have hT : IsOpen T := hgU.continuousOn.isOpen_inter_preimage hU hV
   have hfT : ∀ i,MapsTo (f i) (closedBall 3 (r i)) T := by
     intro i x hx
     exact ⟨hinto i x hx,hKV ⟨f i x,mem_iUnion.mpr ⟨i,x,hx,rfl⟩,rfl⟩⟩
   obtain ⟨τ,hτ,hτη,houter⟩ := outer_packing_uniform_bubble_into (N := N) hm (by omega) t δ c hD hDL
     hT r f hf hfT hd hη
   obtain ⟨σ,hσ,_hση,hbubble⟩ := exists_uniform_cubic_bubble_ball m hAS hS hB hp hN hm.le
     t δ hc hD hD0 hr₀ hW (h0W (mem_singleton 0)) hτ
   let ε : ℝ := min τ σ/2
   have hε : 0<ε := half_pos (lt_min hτ hσ)
   have hετ : ε≤τ := (half_le_self (le_of_lt (lt_min hτ hσ))).trans (min_le_left _ _)
   have hεσ : ε≤σ := (half_le_self (le_of_lt (lt_min hτ hσ))).trans (min_le_right _ _)
   obtain ⟨g,hg,hgT,hdg⟩ := houter ε ⟨hε,hετ⟩
   obtain ⟨g₀,hg₀,hg₀W⟩ := hbubble ε ⟨hε,hεσ⟩
   obtain ⟨hgf,hdgf⟩ := postcompose_form_packing (fun i => closedBall 3 (r i))
     (fun _ => successorStandardForm 2)
     (cubicOuterBubbleForm (A := A) (B := B) L S (m+1) p N t δ c D ε)
     (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε))
     hU firstToDistinguished hgU.contMDiffOn firstToDistinguished_isEmbedding (by
       intro z hz v w
       simp only [mfderiv_eq_fderiv]
       exact firstToDistinguished_curvature hAS hS hB (by omega) t δ c D hε.ne' hz v w)
     g hg (fun i x hx => (hgT i hx).1) hdg
   refine ⟨ε,⟨hε,hετ.trans hτη⟩,g₀,fun i => firstToDistinguished ∘ g i,hg₀,hgf,?_,hdgf⟩
   intro i
   exact hVW.symm.mono (image_subset_iff.mpr hg₀W)
     (image_subset_iff.mpr (fun x hx => (hgT i hx).2))

 theorem cubicBubblePolynomial_complex_smooth {L S A B m p N : ℕ} (t δ : ℝ) (ε : ℂ) :
     ContDiff ℂ ∞ (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) := by
   exact (cubicBubblePolynomial_joint_smooth (A := A) (B := B) L S m p N t δ).comp
     (f := fun z : Option (Fin 3) → ℂ => (ε,z)) (contDiff_const.prodMk contDiff_id)

 theorem cubic_bubble_target_packing {A B L S m p N k : ℕ}
     (hL : 0<L) (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (hm : m+1<p) (t δ : ℝ) {r₀ : ℝ} (hr₀ : r₀<(m+1:ℕ)/(L:ℝ))
     (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient)
     (hf : ∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
       (outerAmbientForm (A := A) (B := B) L S (1/((L:ℝ)*Real.pi)) t δ) (f i))
     (hinto : ∀ i,∀ x∈closedBall 3 (r i),(f i x).2≠0)
     (hd : Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r i)) (f j '' closedBall 3 (r j)))) :
     HasPacking 3 (k+1) 1 (Fin.cons r₀ r) := by
   have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
   let D : ℝ → ℝ := fun ε => (1-ε)/L
   have hD : ContDiff ℝ ∞ D := (contDiff_const.sub contDiff_id).div_const _
   have hD0 : D 0=1/L := by simp [D]
   have hnorm : D 0*(1/Real.pi)=1/((L:ℝ)*Real.pi) := by rw [hD0]; ring
   have hcap : Real.pi*(D 0*((m+1:ℕ)*(1/Real.pi)))=(m+1:ℕ)/(L:ℝ) := by
     rw [hD0]
     field_simp
   obtain ⟨ε,hε,g₀,g,hg₀,hg,hd₀,hdg⟩ := exists_cubic_bubble_separated hAS hS hB hp hN hm t δ
     (one_div_pos.mpr Real.pi_pos) hD (by rw [hD0]; positivity)
     (by rw [hD0]; field_simp) (by rwa [hcap]) r f (by simpa only [hnorm] using hf) hinto hd
     (show (0:ℝ)<1/2 by norm_num)
   let P := cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε
   have hP : ContDiff ℂ ∞ P := cubicBubblePolynomial_complex_smooth t δ ε
   have hPn : ∀ z,z≠0 → P z≠0 := fun z hz =>
     cubicBubblePolynomial_nonzero L S (m+1) p N t δ (Complex.ofReal_ne_zero.mpr hε.1.ne') hz
   have hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^L•P z :=
     cubicBubblePolynomial_homogeneous hAS hS hB (by omega) p N t δ ε
   obtain ⟨G,hG,hGe,hGin,hGω⟩ := exists_degree_polynomial_target_embedding hP hPn hPs
     (one_div_pos.mpr Real.pi_pos) (show 0≤D ε by dsimp [D]; apply div_nonneg <;> linarith [hε.2])
     (show (L:ℝ)*D ε<1 by dsimp [D]; rw [mul_div_cancel₀ _ hLr.ne']; linarith [hε.1])
   let F : Fin (k+1) → Ambient 3 → Ambient 3 := Fin.cons g₀ g
   have hF : ∀ i : Fin (k+1),FormNeighborhoodEmbedding (closedBall 3 ((Fin.cons r₀ r : Fin (k+1) → ℝ) i))
       (fun _ => successorStandardForm 2) (degreeAffineForm (L:ℝ) P (1/Real.pi) (D ε)) (F i) := by
     intro i
     exact Fin.cases hg₀ hg i
   have hFd : Pairwise (fun i j => Disjoint (F i '' closedBall 3 ((Fin.cons r₀ r : Fin (k+1) → ℝ) i))
       (F j '' closedBall 3 ((Fin.cons r₀ r : Fin (k+1) → ℝ) j))) := by
     intro i
     refine Fin.cases ?_ (fun i => ?_) i
     · intro j
       refine Fin.cases (fun hij => False.elim (hij rfl)) (fun j _ => hd₀ j) j
     · intro j
       refine Fin.cases (fun _ => (hd₀ i).symm) (fun j hij => ?_) j
       exact hdg (fun he => hij (congrArg Fin.succ he))
   obtain ⟨hcomp,hdcomp⟩ := postcompose_form_packing (fun i => closedBall 3 ((Fin.cons r₀ r : Fin (k+1) → ℝ) i))
     (fun _ => successorStandardForm 2) (degreeAffineForm (L:ℝ) P (1/Real.pi) (D ε))
     (fun _ => successorStandardForm 2) isOpen_univ G hG.contMDiff.contMDiffOn
     (hGe.comp Topology.IsEmbedding.subtypeVal) (by
       intro x _hx v w
       rw [mfderiv_eq_fderiv]
       exact (successorStandardForm_apply 2 (fderiv ℝ G x v) (fderiv ℝ G x w)).trans
         (hGω x v w)) F hF (fun _ _ _ => mem_univ _) hFd
   refine ⟨fun i => G ∘ F i,fun i => isBallEmbedding_iff_formNeighborhoodEmbedding.mpr (hcomp i),?_,?_⟩
   · intro i y hy
     obtain ⟨x,_hx,rfl⟩ := hy
     simpa only [mul_one_div_cancel Real.pi_ne_zero,Function.comp_apply] using hGin (F i x)
   · intro i j hij
     exact hdcomp hij

 theorem exists_bubble_integer_orders {r a : ℝ} (hr : 0≤r) (hra : r<a) :
     ∃ Q : ℕ,∀ L S : ℕ,Q<L → S≤L → (S:ℝ)=(L:ℝ)*(1-a) →
       ∃ m p N : ℕ,m+1<p ∧ p<L-S ∧ p<N ∧ r<(m+1:ℕ)/(L:ℝ) := by
   obtain ⟨Q,hQ⟩ := exists_nat_gt (3/(a-r))
   refine ⟨Q,?_⟩
   intro L S hQL hSL hS
   have hL : 0<(L:ℝ) := by exact_mod_cast (show 0<L by omega)
   have hδ : 0<a-r := sub_pos.mpr hra
   have hgap : 3<(L:ℝ)*(a-r) := (div_lt_iff₀ hδ).mp (hQ.trans (by exact_mod_cast hQL))
   let m : ℕ := ⌊r*(L:ℝ)⌋₊
   have hmle : (m:ℝ)≤r*(L:ℝ) := Nat.floor_le (mul_nonneg hr hL.le)
   have hmlt : r*(L:ℝ)<(m:ℝ)+1 := Nat.lt_floor_add_one _
   have he : ((L-S:ℕ):ℝ)=(L:ℝ)*a := by rw [Nat.cast_sub hSL,hS]; ring
   refine ⟨m,m+2,m+3,by omega,?_,by omega,?_⟩
   · apply (Nat.cast_lt (α := ℝ)).mp
     push_cast
     rw [he]
     nlinarith
   · apply (lt_div_iff₀ hL).mpr
     exact_mod_cast hmlt

 theorem actual_six_standard_packing {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3)
    {r₀ : ℝ} (hr₀ : 0≤r₀) (hr₀a : r₀<(a:ℝ)) :
    HasPacking 3 (N+1) 1 (Fin.cons r₀ r') := by
   obtain ⟨Q,hQ⟩ := exists_bubble_integer_orders hr₀ hr₀a
   obtain ⟨L,A,B,S,hQL,hL,_hA,_hS0,hAS,_hAB,_hSB,hB,hS,heS,t,δ,_ht,_hδ,f,hf,hinto,hd⟩ :=
     actual_six_quadric_polynomial_packing_large Q r r' hr hr' hrr ha ha1 hrs hvol
   obtain ⟨m,p,M,hmp,hp,hM,hcap⟩ := hQ L S hQL (by omega) heS
   exact cubic_bubble_target_packing hL hAS hS hB hp hM hmp t δ hcap r' f hf hinto hd

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open scoped Topology
open Set Function MeasureTheory
open scoped Manifold
open Manifold
section

 theorem planeRotate_fderiv (θ a : ℝ) (z v : Plane) :
    fderiv ℝ (fun p : ℝ × Plane => planeRotate p.1 p.2) (θ,z) (a,v)=
      planeRotate θ v+a • (-(planeRotate θ z).2,(planeRotate θ z).1) := by
  have hθ := hasFDerivAt_fst (𝕜 := ℝ) (p := (θ,z))
  have hz := hasFDerivAt_snd (𝕜 := ℝ) (p := (θ,z))
  have hc := (Real.hasDerivAt_cos θ).comp_hasFDerivAt (θ,z) hθ
  have hs := (Real.hasDerivAt_sin θ).comp_hasFDerivAt (θ,z) hθ
  have h1 := (hc.mul hz.fst).sub (hs.mul hz.snd)
  have h2 := (hs.mul hz.fst).add (hc.mul hz.snd)
  have he := congrArg (fun L => L (a,v)) (h1.prodMk h2).fderiv
  change fderiv ℝ (fun p : ℝ × Plane => planeRotate p.1 p.2) (θ,z) (a,v)=_ at he
  rw [he]
  ext <;> simp [planeRotate,smul_eq_mul] <;> ring

 theorem planarLiouville_rotation (θ a : ℝ) (z v : Plane) :
    linearLiouville planarArea (planeRotate θ z)
      (planeRotate θ v+a • (-(planeRotate θ z).2,(planeRotate θ z).1))=
        linearLiouville planarArea z v+a*(radialArea z/(2*Real.pi)) := by
  change (1/2:ℝ)*planarArea (planeRotate θ z)
    (planeRotate θ v+a • (-(planeRotate θ z).2,(planeRotate θ z).1))=_
  have he : planarArea (planeRotate θ z) (planeRotate θ v)=planarArea z v := by
    calc
      _=(Real.sin θ^2+Real.cos θ^2)*planarArea z v := by
        simp only [planarArea_apply,planeRotate]
        ring
      _=_ := by rw [Real.sin_sq_add_cos_sq,one_mul]
  have hr : planarArea (planeRotate θ z) (-(planeRotate θ z).2,(planeRotate θ z).1)=radiusSq z := by
    rw [← radiusSq_planeRotate θ z]
    simp only [planarArea_apply,radiusSq]
    ring
  rw [map_add,map_smul,he,hr]
  change (1/2:ℝ)*(planarArea z v+a*radiusSq z)=
    (1/2:ℝ)*planarArea z v+a*(Real.pi*radiusSq z/(2*Real.pi))
  field_simp [Real.pi_ne_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 theorem planarLiouville_gauge {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u : E × Plane) :
    linearLiouville planarArea (planeRotate (2*Real.pi*f x.1) x.2)
      (fderiv ℝ (fun y : E × Plane => planeRotate (2*Real.pi*f y.1) y.2) x u)=
        linearLiouville planarArea x.2 u.2+radialArea x.2*fderiv ℝ f x.1 u.1 := by
  have h₁ : HasFDerivAt (fun y : E × Plane => 2*Real.pi*f y.1)
      ((2*Real.pi) • (fderiv ℝ f x.1).comp (ContinuousLinearMap.fst ℝ E Plane)) x :=
    ((hf.differentiable (by simp) x.1).hasFDerivAt.comp x
      (hasFDerivAt_fst (𝕜 := ℝ) (p := x))).const_mul _
  have hpair := h₁.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := x))
  have hc := (planeRotate_smooth.differentiable (by simp) _).hasFDerivAt.comp x hpair
  change HasFDerivAt (fun y : E × Plane => planeRotate (2*Real.pi*f y.1) y.2) _ x at hc
  rw [hc.fderiv]
  change linearLiouville planarArea (planeRotate (2*Real.pi*f x.1) x.2)
    (fderiv ℝ (fun p : ℝ × Plane => planeRotate p.1 p.2) (2*Real.pi*f x.1,x.2)
      (2*Real.pi*fderiv ℝ f x.1 u.1,u.2))=_
  rw [planeRotate_fderiv,planarLiouville_rotation]
  field_simp [Real.pi_ne_zero]

end
section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 def radialOneFormPotential (α : E → E →L[ℝ] ℝ) (x : E) : ℝ :=
  ∫ t in (0:ℝ)..1,α (t • x) x

 theorem radialOneFormPotential_smooth {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) : ContDiff ℝ ∞ (radialOneFormPotential α) := by
  exact contDiff_fixed_integral ((hα.comp (contDiff_fst.smul contDiff_snd)).clm_apply contDiff_snd)

omit [FiniteDimensional ℝ E] in
 theorem closedOneForm_derivative_symmetric {α : E → E →L[ℝ] ℝ}
    (hclosed : ∀ x,euclideanExteriorOneForm α x=0) (z v w : E) :
    fderiv ℝ α z v w=fderiv ℝ α z w v := by
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v w) (hclosed z)
  simpa only [euclideanExteriorOneForm,sub_apply,
    ContinuousLinearMap.flip_apply,zero_apply,sub_eq_zero] using he

omit [FiniteDimensional ℝ E] in
 theorem radialOneFormIntegrand_hasFDerivAt {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (t : ℝ) (x : E) :
    HasFDerivAt (fun y => α (t • y) y)
      (t • (fderiv ℝ α (t • x)).flip x + α (t • x)) x := by
  have hd := ((hα.differentiable (by simp) (t • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul t)).clm_apply (hasFDerivAt_id x)
  apply hd.congr_fderiv
  ext v
  change α (t • x) v+fderiv ℝ α (t • x) (t • v) x=
    t*(fderiv ℝ α (t • x) v x)+α (t • x) v
  simp only [map_smul,smul_apply,smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
 theorem radialOneFormIntegrand_fderiv_continuous {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (x : E) :
    Continuous (fun t : ℝ => fderiv ℝ (fun y => α (t • y) y) x) := by
  simp_rw [(radialOneFormIntegrand_hasFDerivAt hα _ _).fderiv]
  have hder : Continuous (fun t : ℝ => fderiv ℝ α (t • x)) :=
    (hα.fderiv_right (m := ∞) (by simp)).continuous.comp (continuous_id.smul continuous_const)
  have hflip := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous.comp hder
  exact (continuous_id.smul (hflip.clm_apply continuous_const)).add
    (hα.continuous.comp (continuous_id.smul continuous_const))

omit [FiniteDimensional ℝ E] in
 theorem radialOneForm_strand_hasDerivAt {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hclosed : ∀ z,euclideanExteriorOneForm α z=0)
    (x v : E) (t : ℝ) : HasDerivAt (fun s : ℝ => s * α (s • x) v)
      (fderiv ℝ (fun y => α (t • y) y) x v) t := by
  have ha : HasDerivAt (fun s : ℝ => α (s • x)) (fderiv ℝ α (t • x) x) t :=
    (hα.differentiable (by simp) (t • x)).hasFDerivAt.comp_hasDerivAt t
      (by simpa using (hasDerivAt_id t).smul_const x)
  have hb := ha.clm_apply (hasDerivAt_const t v)
  have hh := (hasDerivAt_id t).mul hb
  apply hh.congr_deriv
  rw [(radialOneFormIntegrand_hasFDerivAt hα t x).fderiv]
  change 1*α (t • x) v+t*(fderiv ℝ α (t • x) x v+α (t • x) 0)=
    t*fderiv ℝ α (t • x) v x+α (t • x) v
  rw [closedOneForm_derivative_symmetric hclosed (t • x) v x,map_zero]
  ring

 theorem radialOneFormPotential_hasFDerivAt {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hclosed : ∀ x,euclideanExteriorOneForm α x=0) (x : E) :
    HasFDerivAt (radialOneFormPotential α) (α x) x := by
  have hf : ContDiff ℝ ∞ (fun p : ℝ × E => α (p.1 • p.2) p.2) :=
    (hα.comp (contDiff_fst.smul contDiff_snd)).clm_apply contDiff_snd
  have hDcont := radialOneFormIntegrand_fderiv_continuous hα x
  have hinter : IntervalIntegrable (fun t : ℝ => fderiv ℝ (fun y => α (t • y) y) x) volume 0 1 :=
    hDcont.intervalIntegrable 0 1
  have he : (∫ t in (0:ℝ)..1,fderiv ℝ (fun y => α (t • y) y) x)=α x := by
    ext v
    rw [ContinuousLinearMap.intervalIntegral_apply hinter]
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => radialOneForm_strand_hasDerivAt hα hclosed x v t)
      ((hDcont.clm_apply continuous_const).intervalIntegrable 0 1)
    simpa using hi
  exact (hasFDerivAt_fixed_integral hf x).congr_fderiv he

 theorem radialOneFormPotential_fderiv {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hclosed : ∀ x,euclideanExteriorOneForm α x=0) (x : E) :
    fderiv ℝ (radialOneFormPotential α) x=α x :=
  (radialOneFormPotential_hasFDerivAt hα hclosed x).fderiv

end
section

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem euclideanExteriorOneForm_df {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    euclideanExteriorOneForm (fderiv ℝ f) x=0 := by
  ext v w
  change fderiv ℝ (fderiv ℝ f) x v w-fderiv ℝ (fderiv ℝ f) x w v=0
  have hs := hf.contDiffAt.isSymmSndFDerivAt (x := x) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  exact sub_eq_zero.mpr (hs.eq v w)

 theorem euclideanExteriorOneForm_sub {α β : E → E →L[ℝ] ℝ} {point : E}
    (hα : DifferentiableAt ℝ α point) (hβ : DifferentiableAt ℝ β point) :
    euclideanExteriorOneForm (α-β) point=
      euclideanExteriorOneForm α point-euclideanExteriorOneForm β point := by
  ext v w
  simp only [euclideanExteriorOneForm,fderiv_sub hα hβ,sub_apply,ContinuousLinearMap.flip_apply]
  ring

 variable [FiniteDimensional ℝ E]
 theorem exists_exact_primitive_comparison {α : F → F →L[ℝ] ℝ} {β : E → E →L[ℝ] ℝ}
    {g : E → F} (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β) (hg : ContDiff ℝ ∞ g)
    (hω : ∀ x,(euclideanExteriorOneForm α (g x)).bilinearComp
      (fderiv ℝ g x) (fderiv ℝ g x)=euclideanExteriorOneForm β x) :
    ∃ f : E → ℝ,ContDiff ℝ ∞ f ∧ ∀ x,primitivePullback α g x=β x+fderiv ℝ f x := by
  let δ := primitivePullback α g-β
  have hδ : ContDiff ℝ ∞ δ := (primitivePullback_smooth hα hg).sub hβ
  have hclosed x : euclideanExteriorOneForm δ x=0 := by
    rw [euclideanExteriorOneForm_sub
      ((primitivePullback_smooth hα hg).differentiable (by simp) x)
      (hβ.differentiable (by simp) x),primitivePullback_exterior hα hg,hω x]
    ext v w
    simp only [sub_apply,zero_apply,sub_self]
  refine ⟨radialOneFormPotential δ,radialOneFormPotential_smooth hδ,?_⟩
  intro x
  rw [radialOneFormPotential_fderiv hδ hclosed]
  change _=β x+(primitivePullback α g x-β x)
  abel

end
section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 def firstLinePrimitive (α : ManifoldOneForm E M) : ManifoldOneForm (E × Plane) (M × Plane) :=
  productCouplingPrimitive planarArea (fun z => (1-radialArea z) • α)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem firstLinePrimitive_apply (α : ManifoldOneForm E M) (x : M × Plane) (u : E × Plane) :
    firstLinePrimitive α x u=linearLiouville planarArea x.2 u.2+(1-radialArea x.2)*α x.1 u.1 := by
  simp only [firstLinePrimitive,productCouplingPrimitive,Pi.add_apply,add_apply,
    productVerticalLiouville_apply,productHorizontalLift_apply,Pi.smul_apply,smul_apply,smul_eq_mul]
  rfl

 theorem firstLinePrimitive_family_smooth {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (fun t => firstLinePrimitive (Γ t)) := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × Plane => 1-radialArea p.2) :=
    contDiff_const.sub (radialArea_smooth.comp contDiff_snd)
  have hb : SmoothOneFormFamily (fun p : ℝ × Plane => Γ p.1) :=
    SmoothOneFormFamily.comp (P := ℝ) (Q := ℝ × Plane) (E := E) (M := M) hΓ contDiff_fst
  change SmoothOneFormFamily (fun t => productCouplingPrimitive planarArea
    (fun z => (1-radialArea z) • Γ t))
  exact productCouplingPrimitive_smooth (E := E) (M := M) (V := Plane) planarArea
    (Γ := fun p : ℝ × Plane => (1-radialArea p.2) • Γ p.1)
    (SmoothOneFormFamily.smul (P := ℝ × Plane) (E := E) (M := M) hb hs)

 theorem firstLinePrimitive_smooth {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α) :
    ContDiff ℝ ∞ (firstLinePrimitive α) := by
  have he : firstLinePrimitive α=(fun x : E × Plane =>
      (linearLiouville planarArea x.2).comp (ContinuousLinearMap.snd ℝ E Plane)+
        (1-radialArea x.2) • (α x.1).comp (ContinuousLinearMap.fst ℝ E Plane)) := by
    funext x
    apply ContinuousLinearMap.ext
    intro u
    exact firstLinePrimitive_apply α x u
  rw [he]
  exact (((linearLiouville_smooth planarArea).comp contDiff_snd).clm_comp contDiff_const).add
    ((contDiff_const.sub (radialArea_smooth.comp contDiff_snd)).smul
      ((hα.comp contDiff_fst).clm_comp contDiff_const))

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

 def firstLineLift (g : E → F) (f : E → ℝ) (x : E × Plane) : F × Plane :=
  (g x.1,planeRotate (2*Real.pi*f x.1) x.2)

 theorem gaugeRotation_smooth {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y : E × Plane => planeRotate (2*Real.pi*f y.1) y.2) := by
  have hf' : ContDiff ℝ ∞ (fun y : E × Plane => f y.1) := hf.comp contDiff_fst
  have hθ : ContDiff ℝ ∞ (fun y : E × Plane => 2*Real.pi*f y.1) := contDiff_const.mul hf'
  have hp : ContDiff ℝ ∞ (fun y : E × Plane => (2*Real.pi*f y.1,y.2)) := hθ.prodMk contDiff_snd
  convert! planeRotate_smooth.comp hp using 1

 theorem firstLineLift_smooth {g : E → F} {f : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (firstLineLift g f) :=
  (hg.comp contDiff_fst).prodMk (gaugeRotation_smooth hf)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
 theorem firstLineLift_inverse {g : E → F} {h : F → E} (hgh : LeftInverse h g) (hhg : RightInverse h g)
    (f : E → ℝ) : LeftInverse (firstLineLift h (fun y => -f (h y))) (firstLineLift g f) ∧
      RightInverse (firstLineLift h (fun y => -f (h y))) (firstLineLift g f) := by
  constructor <;> intro x <;> apply Prod.ext
  · exact hgh x.1
  · simp only [firstLineLift,planeRotate_comp]
    rw [hgh x.1]
    rw [show 2*Real.pi*(-f x.1)+2*Real.pi*f x.1=0 by ring,planeRotate_zero]
  · exact hhg x.1
  · simp only [firstLineLift,planeRotate_comp]
    rw [show 2*Real.pi*f (h x.1)+2*Real.pi*(-f (h x.1))=0 by ring,planeRotate_zero]

 theorem firstLineLift_isEmbedding {g : E → F} {h : F → E} {f : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (hf : ContDiff ℝ ∞ f)
    (hgh : LeftInverse h g) (hhg : RightInverse h g) : Topology.IsEmbedding (firstLineLift g f) := by
  let e : E × Plane ≃ₜ F × Plane :=
    { toEquiv := ⟨firstLineLift g f,firstLineLift h (fun y => -f (h y)),
        (firstLineLift_inverse hgh hhg f).1,(firstLineLift_inverse hgh hhg f).2⟩
      continuous_toFun := (firstLineLift_smooth hg hf).continuous
      continuous_invFun := (firstLineLift_smooth hh (hf.comp hh).neg).continuous }
  exact e.isEmbedding

 theorem firstLineLift_primitive {α : F → F →L[ℝ] ℝ} {β : E → E →L[ℝ] ℝ}
    {g : E → F} {f : E → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x,primitivePullback α g x=β x+fderiv ℝ f x) :
    primitivePullback (firstLinePrimitive α) (firstLineLift g f)=
      firstLinePrimitive β+fderiv ℝ (f ∘ Prod.fst) := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  have hrot : ContDiff ℝ ∞ (fun y : E × Plane => planeRotate (2*Real.pi*f y.1) y.2) :=
    gaugeRotation_smooth hf
  have hD := (((hg.differentiable (by simp) x.1).hasFDerivAt.comp x
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x))).prodMk (hrot.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (firstLineLift g f) x=_ at hD
  change firstLinePrimitive α (firstLineLift g f x) (fderiv ℝ (firstLineLift g f) x u)=_
  rw [firstLinePrimitive_apply,hD]
  change linearLiouville planarArea (planeRotate (2*Real.pi*f x.1) x.2)
    (fderiv ℝ (fun y : E × Plane => planeRotate (2*Real.pi*f y.1) y.2) x u)+
    (1-radialArea (planeRotate (2*Real.pi*f x.1) x.2))*α (g x.1) (fderiv ℝ g x.1 u.1)=_
  rw [planarLiouville_gauge hf,radialArea_planeRotate]
  have he' := congrArg (fun L : E →L[ℝ] ℝ => L u.1) (he x.1)
  change α (g x.1) (fderiv ℝ g x.1 u.1)=β x.1 u.1+fderiv ℝ f x.1 u.1 at he'
  rw [he']
  have hdf := ((hf.differentiable (by simp) x.1).hasFDerivAt.comp x
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x))).fderiv
  simp only [Pi.add_apply,add_apply,firstLinePrimitive_apply,hdf,ContinuousLinearMap.comp_apply,
    ]
  change _=linearLiouville planarArea x.2 u.2+(1-radialArea x.2)*β x.1 u.1+fderiv ℝ f x.1 u.1
  ring

 theorem firstLineLift_exterior {α : F → F →L[ℝ] ℝ} {β : E → E →L[ℝ] ℝ}
    {g : E → F} {f : E → ℝ} (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x,primitivePullback α g x=β x+fderiv ℝ f x) (x : E × Plane) :
    (euclideanExteriorOneForm (firstLinePrimitive α) (firstLineLift g f x)).bilinearComp
      (fderiv ℝ (firstLineLift g f) x) (fderiv ℝ (firstLineLift g f) x)=
        euclideanExteriorOneForm (firstLinePrimitive β) x := by
  have hdf : ContDiff ℝ ∞ (f ∘ (Prod.fst : E × Plane → E)) := hf.comp contDiff_fst
  have hz := euclideanExteriorOneForm_df hdf x
  rw [← primitivePullback_exterior (firstLinePrimitive_smooth hα) (firstLineLift_smooth hg hf),
    firstLineLift_primitive hg hf he,euclideanExteriorOneForm_add
      ((firstLinePrimitive_smooth hβ).differentiable (by simp) x)
      ((hdf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x),hz]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change euclideanExteriorOneForm (firstLinePrimitive β) x u v+(0:ℝ)=_
  exact add_zero _

end

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

 def firstLineBaseMap (g : M → N) (x : M × Plane) : N × Plane := (g x.1,x.2)

 theorem firstLineBaseMap_smooth {g : M → N} (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g) :
    ContMDiff 𝓘(ℝ,E × Plane) 𝓘(ℝ,F × Plane) ∞ (firstLineBaseMap g) := by
  rw [show 𝓘(ℝ,F × Plane)=(𝓘(ℝ,F)).prod 𝓘(ℝ,Plane) from modelWithCornersSelf_prod]
  exact (hg.comp flatProduct_fst_smooth).prodMk flatProduct_snd_smooth

 theorem firstLineBaseMap_derivative {g : M → N} (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g)
    (x : M × Plane) :
    manifoldMapDifferential (E := F × Plane) (F := E × Plane) (firstLineBaseMap g) x=
      (manifoldMapDifferential (E := F) (F := E) g x.1).prodMap
        (ContinuousLinearMap.id ℝ Plane) := by
  have hf := ((hg.comp flatProduct_fst_smooth).mdifferentiable (by simp) x).hasMFDerivAt
  have hs := ((flatProduct_snd_smooth (E := E) (M := M) (V := Plane)).mdifferentiable (by simp) x).hasMFDerivAt
  have hd : HasMFDerivAt 𝓘(ℝ,E × Plane) 𝓘(ℝ,F × Plane) (firstLineBaseMap g) x
      ((mfderiv 𝓘(ℝ,E × Plane) 𝓘(ℝ,F) (g ∘ Prod.fst) x).prod
        (mfderiv 𝓘(ℝ,E × Plane) 𝓘(ℝ,Plane) Prod.snd x)) := by
    rw [show 𝓘(ℝ,F × Plane)=(𝓘(ℝ,F)).prod 𝓘(ℝ,Plane) from modelWithCornersSelf_prod]
    exact hf.prodMk hs
  apply hd.mfderiv.trans
  erw [mfderiv_comp x (hg.mdifferentiable (by simp) x.1)
    (flatProduct_fst_smooth.mdifferentiable (by simp) x),flatProduct_fst_derivative,flatProduct_snd_derivative]
  rfl

 theorem firstLineBaseMap_primitive {g : M → N} (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g)
    (α : ManifoldOneForm F N) (x : M × Plane) :
    manifoldPullbackOneForm (fun _ => firstLinePrimitive α) (firstLineBaseMap g) 0 x=
      firstLinePrimitive (manifoldPullbackOneForm (E := F) (F := E) (fun _ => α) g 0) x := by
  apply ContinuousLinearMap.ext
  intro v
  change firstLinePrimitive α (firstLineBaseMap g x)
    (manifoldMapDifferential (E := F × Plane) (F := E × Plane) (firstLineBaseMap g) x v)=_
  rw [firstLineBaseMap_derivative hg,firstLinePrimitive_apply,firstLinePrimitive_apply]
  rfl

end PackingSufficiencySupport.Hamiltonian
end

end OAI
