import OAI.MathematicalPhysics.Elasticity.Smoothing

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter TemperedDistribution
open scoped BigOperators SchwartzMap Topology
namespace Elasticity
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityDistribution (Coeff Dist LocalEq AugHilbert leadingRd leadingSd normald)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityNegativeOrder (sobNorm)
open ElasticityCGO

theorem dn_smooth_transport_column {Ω B B' B₀ : Set X}
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
    (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (R : ℝ) (hR : 1≤R) (hKR : closure Ω⊆Metric.closedBall 0 R)
    (hBR : B⊆Metric.ball 0 R) (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
    (χ g η : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
    (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
    (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B')
    (hcη : HasCompactSupport (η : X → ℂ)) (hsη : tsupport (η : X → ℂ)⊆Metric.ball 0 R)
    (hη : EqOn (η : X → ℂ) 1 B)
    (a : ℕ → Amplitude Smooth)
    (ha : PhysicalColumn R hR α β (smoothOfReal (lam 0) (hl 0)) (smoothOfReal (m 0) (hm 0)) a)
    (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(ElasticityAugmented.div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R))
    (hB₀ : IsOpen B₀) (hKB₀ : closure Ω⊆B₀)
    (ρ : Smooth) (hcρ : HasCompactSupport (ρ : X → ℂ))
    (hρs : tsupport (ρ : X → ℂ)⊆B') (hρ1 : EqOn (ρ : X → ℂ) 1 B₀) :
    let θ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
    ∃ v : Fin 4 → Smooth,
      (∀ i,tsupport ((v i-(Fin.cons (a 0).2 (a 0).1 : Fin 4 → Smooth) i : Smooth) : X → ℂ)⊆closure Ω) ∧
      (∀ i,EqOn (leadingR coord θ (smoothOfReal (lam 1) (hl 1)) (smoothOfReal (m 1) (hm 1))
        (fun j => v j.succ) (v 0) i).val 0 B') ∧
      EqOn (leadingS coord θ (smoothOfReal (lam 1) (hl 1)) (smoothOfReal (m 1) (hm 1))
        (fun j => v j.succ) (v 0)).val 0 B' ∧
      normal θ (fun j => v j.succ)=0 := by
  intro θ
  let l := smoothOfReal (lam 1) (hl 1)
  let μ := smoothOfReal (m 1) (hm 1)
  let L : Coeff := ⟨l,(hcll 1).growth⟩
  let M : Coeff := ⟨μ,(hclm 1).growth⟩
  have hm0 : ∀ x,(μ : X → ℂ) x≠0 := fun x => Complex.ofReal_ne_zero.mpr (hp 1 x).1.ne'
  have he0 : ∀ x,((l+μ+μ : Smooth) : X → ℂ) x≠0 := by
    intro x
    change (lam 1 x : ℂ)+(m 1 x : ℂ)+(m 1 x : ℂ)≠0
    exact_mod_cast (real_longitudinal_positive (lam 1) (m 1) (hp 1) x).ne'
  let n := ElasticityDistribution.inverseCoeff μ (hclm 1) hm0
  let o := ElasticityDistribution.inverseCoeff (l+μ+μ) (((hcll 1).add (hclm 1)).add (hclm 1)) he0
  have hn : n*M=1 := ElasticityDistribution.inverseCoeff_mul μ (hclm 1) hm0
  have ho : o*(L+M+M)=1 := by
    apply Subtype.ext
    exact ElasticityCoeffBounds.reciprocal_mul (l+μ+μ) he0
  have hne : θ≠0 := by
    intro hz
    apply hα
    ext i
    change α i=0
    have hh := congrArg Complex.re (congrFun hz i)
    simpa [θ] using hh
  obtain ⟨W,hRW,hS,hN,hE⟩ := dn_weak_transport_column hΩ hOB hB hBB hB' hsub hcl
    R hR hKR hBR α β hα hθ lam m hl hm hp hcll hclm he hDN χ g η hcχ hc hs hχ hg
    hcη hsη hη a ha h₀ hrec
  obtain ⟨v,hv,hvs⟩ := ElasticityDistribution.weak_leading_smooth hOB.isCompact_closure hB₀ hKB₀
    θ hθ hne L M n o hn ho W (localizedLeading R hR a η) hE hRW hS
    ρ (smooth_coe ρ) hcρ hρs hρ1
  have hR' : ∀ i,LocalEq B' (leadingRd θ L M (fun j => (v j.succ : Dist)) (v 0 : Dist) i) 0 := by
    simpa only [hv] using hRW
  have hS' : LocalEq B' (leadingSd θ L M (fun j => (v j.succ : Dist)) (v 0 : Dist)) 0 := by
    simpa only [hv] using hS
  have hN' : LocalEq B' (normald θ (fun j => (v j.succ : Dist))) 0 := by
    simpa only [hv] using hN
  exact ElasticityDistribution.smooth_column_patch hB' hcl θ L M v (localizedLeading R hR a η)
    (Fin.cons (a 0).2 (a 0).1) hvs
    (fun i => (localizedLeading_eqOn hB R hR hBR a η hcη hη i).mono hsub) hR' hS' hN' h₀
end Elasticity

end
end
section
noncomputable section
open Set
open scoped BigOperators
namespace Elasticity
open ElasticityAugmented ElasticityCGO
open ElasticityCoeffBounds (ExteriorConstant)
/-- Three actual transferred physical leading columns, in the same constrained
fiber as the original globally independent frame. The new columns need not be
assumed independent. -/
theorem dn_common_leading_frame {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
    (r₀ : ℝ) (hr₀ : 1≤r₀) (hK : closure Ω⊆Metric.closedBall 0 r₀)
    (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) :
    let θ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
    let l := fun q => smoothOfReal (lam q) (hl q)
    let μ := fun q => smoothOfReal (m q) (hm q)
    let r := positiveRoot (m 0) (hm 0) (fun x => (hp 0 x).1)
    let hr := positiveRoot_nonzero (m 0) (hm 0) (fun x => (hp 0 x).1)
    ∃ a : Fin 2 → Fin 3 → Amplitude Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ q ν,normal θ (a q ν).1=0) ∧
      (∀ q ν i,EqOn ((leadingR coord θ (l q) (μ q) (a q ν).1 (a q ν).2 i : Smooth) : X → ℂ) 0 (Metric.ball 0 (r₀+3))) ∧
      (∀ q ν,EqOn ((leadingS coord θ (l q) (μ q) (a q ν).1 (a q ν).2 : Smooth) : X → ℂ) 0 (Metric.ball 0 (r₀+3))) ∧
      (∀ ν i,tsupport ((((Fin.cons (a 1 ν).2 (a 1 ν).1 : Fin 4 → Smooth) i-
        (Fin.cons (a 0 ν).2 (a 0 ν).1 : Fin 4 → Smooth) i : Smooth)) : X → ℂ)⊆closure Ω) ∧
      ∀ ν x,((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (changeP r (a 0 ν).1 i : X → ℂ) x),
          (changeS (l 0+μ 0) r hr (a 0 ν).1 (a 0 ν).2 : X → ℂ) x) := by
  intro θ l μ r hr
  let R := r₀+7
  have hR : 1≤R := by dsimp [R]; linarith
  have hne : θ≠0 := by
    intro hz
    apply hα
    ext i
    change α i=0
    have hh := congrArg Complex.re (congrFun hz i)
    simpa [θ] using hh
  have hC : IsCompact (closure (Metric.ball (0 : X) R)) :=
    (isCompact_closedBall (0 : X) R).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  obtain ⟨a,B,hn,hL,hrec,hB⟩ := exists_real_physical_series Metric.isOpen_ball hC θ hθ hne
    (lam 0) (m 0) (hl 0) (hm 0) (hp 0)
  let χ : Fin 5 → Smooth := fun i => ⟨fiveCutoff r₀ hr₀ i,fiveCutoff_smooth r₀ hr₀ i⟩
  have hball {s t : ℝ} (hst : s<t) : Metric.closedBall (0 : X) s⊆Metric.ball 0 t :=
    Metric.closedBall_subset_ball hst
  have hcb : closure Ω⊆Metric.ball 0 (r₀+3) := hK.trans (hball (by linarith))
  have hpc (ν : Fin 3) : PhysicalColumn R hR α β (l 0) (μ 0) (a ν) := by
    apply physical_column_of_recursion R hR α β hα hθ (l 0) (μ 0) (hcll 0) (hclm 0)
      (fun x => Complex.conj_ofReal _) (fun x => Complex.conj_ofReal _)
      (fun x => Complex.ofReal_ne_zero.mpr (hp 0 x).1.ne') (fun x => ?_)
      (a ν) (hL ν).1 (hn ν) (fun j _ => hrec ν j)
    change (lam 0 x : ℂ)+(m 0 x : ℂ)+(m 0 x : ℂ)≠0
    exact_mod_cast (real_longitudinal_positive (lam 0) (m 0) (hp 0) x).ne'
  have hex (ν : Fin 3) := dn_smooth_transport_column hΩ hOB Metric.isOpen_ball Metric.isBounded_ball
    (B := Metric.ball 0 (r₀+5)) (B' := Metric.ball 0 (r₀+3)) Metric.isOpen_ball
    (Metric.ball_subset_ball (by linarith)) hcb R hR
    (hK.trans (Metric.closedBall_subset_closedBall (by dsimp [R]; linarith)))
    (Metric.ball_subset_ball (by dsimp [R]; linarith)) α β hα hθ lam m hl hm hp hcll hclm he hDN
    (χ 4) (χ 2) (χ 4) (fiveCutoff_compact r₀ hr₀ 4) (fiveCutoff_compact r₀ hr₀ 2)
    ((fiveCutoff_support r₀ hr₀ 2).trans (hball (by norm_num; linarith)))
    (fun x hx => fiveCutoff_one r₀ hr₀ 4 (by convert Metric.ball_subset_closedBall hx using 1; norm_num [add_assoc]))
    (fun x hx => fiveCutoff_one r₀ hr₀ 2 (by convert Metric.ball_subset_closedBall hx using 1; norm_num [add_assoc]))
    (fiveCutoff_compact r₀ hr₀ 4) ((fiveCutoff_support r₀ hr₀ 4).trans (hball (by norm_num; dsimp [R]; linarith)))
    (fun x hx => fiveCutoff_one r₀ hr₀ 4 (by convert Metric.ball_subset_closedBall hx using 1; norm_num [add_assoc]))
    (a ν) (hpc ν) (hn ν)
    (fun j _ x _ => congrArg (fun f : Smooth => (f : X → ℂ) x) (hrec ν j).2.2)
    (B₀ := Metric.ball 0 (r₀+1)) Metric.isOpen_ball (hK.trans (hball (by linarith)))
    (χ 0) (fiveCutoff_compact r₀ hr₀ 0)
    ((fiveCutoff_support r₀ hr₀ 0).trans (hball (by norm_num)))
    (fun x hx => fiveCutoff_one r₀ hr₀ 0 (by convert Metric.ball_subset_closedBall hx using 1; norm_num [add_assoc]))
  choose v hvs hvR hvS hvn using hex
  let A : Fin 2 → Fin 3 → Amplitude Smooth := ![(fun ν => a ν 0),fun ν => ((fun i => v ν i.succ),v ν 0)]
  have hR₀ (ν i) : EqOn ((leadingR coord θ (l 0) (μ 0) (a ν 0).1 (a ν 0).2 i : Smooth) : X → ℂ) 0
      (Metric.ball 0 (r₀+3)) := by
    have hh := congrFun (hL ν).1 i
    dsimp only [localAmp] at hh
    rw [← restrict_leadingR Metric.isOpen_ball] at hh
    intro x hx
    exact (restrictSmooth_zero_iff _ _).mp hh x (Metric.ball_subset_ball (by dsimp [R]; linarith) hx)
  have hS₀ (ν) : EqOn ((leadingS coord θ (l 0) (μ 0) (a ν 0).1 (a ν 0).2 : Smooth) : X → ℂ) 0
      (Metric.ball 0 (r₀+3)) := by
    have hh := (hL ν).2
    dsimp only [localAmp] at hh
    rw [← restrict_leadingS Metric.isOpen_ball] at hh
    intro x hx
    exact (restrictSmooth_zero_iff _ _).mp hh x (Metric.ball_subset_ball (by dsimp [R]; linarith) hx)
  refine ⟨A,B,?_,?_,?_,?_,hB⟩
  · intro q ν
    fin_cases q
    · exact hn ν
    · exact hvn ν
  · intro q ν i
    fin_cases q
    · exact hR₀ ν i
    · exact hvR ν i
  · intro q ν
    fin_cases q
    · exact hS₀ ν
    · exact hvS ν
  · intro ν i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hvs ν 0
    · exact hvs ν j.succ
end Elasticity

end
end
section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityAugmented
lemma smooth_sum_eval {ι : Type*} [Fintype ι] (f : ι → Smooth) (x : X) :
    ((∑ i,f i : Smooth) : X → ℂ) x=∑ i,(f i : X → ℂ) x := by
  exact map_sum ((Pi.evalRingHom (fun _ : X => ℂ) x).comp Smooth.val.toRingHom) f Finset.univ
lemma eqOn_coord {U : Set X} (hU : IsOpen U) (f g : Smooth)
    (he : EqOn (f : X → ℂ) g U) (i : Fin 3) :
    EqOn (coord i f : X → ℂ) (coord i g) U := by
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [← localCoord_restrict hU,← localCoord_restrict hU,(restrictSmooth_eq_iff U f g).mpr he]
lemma eqOn_direction {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (f g : Smooth)
    (he : EqOn (f : X → ℂ) g U) :
    EqOn (direction (A := Smooth) coord θ f : X → ℂ) (direction (A := Smooth) coord θ g) U := by
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [restrict_direction hU,restrict_direction hU,(restrictSmooth_eq_iff U f g).mpr he]
lemma eqOn_logarithmicGrad {U : Set X} (hU : IsOpen U) (r₀ r₁ : Smooth)
    (hr₀ : ∀ x,(r₀ : X → ℂ) x≠0) (hr₁ : ∀ x,(r₁ : X → ℂ) x≠0)
    (he : EqOn (r₀ : X → ℂ) r₁ U) (i : Fin 3) :
    EqOn (logarithmicGrad r₀ hr₀ i : X → ℂ) (logarithmicGrad r₁ hr₁ i) U := by
  intro x hx
  change 2*((r₀ : X → ℂ) x)⁻¹*(coord i r₀ : X → ℂ) x=
    2*((r₁ : X → ℂ) x)⁻¹*(coord i r₁ : X → ℂ) x
  rw [he hx,eqOn_coord hU r₀ r₁ he i hx]
lemma eqOn_physical_change {U : Set X} (hU : IsOpen U) (k₀ k₁ r₀ r₁ : Smooth)
    (hr₀ : ∀ x,(r₀ : X → ℂ) x≠0) (hr₁ : ∀ x,(r₁ : X → ℂ) x≠0)
    (a₀ a₁ : Fin 3 → Smooth) (b₀ b₁ : Smooth)
    (hk : EqOn (k₀ : X → ℂ) k₁ U) (hr : EqOn (r₀ : X → ℂ) r₁ U)
    (ha : ∀ i,EqOn (a₀ i : X → ℂ) (a₁ i) U) (hb : EqOn (b₀ : X → ℂ) b₁ U) :
    (∀ i,EqOn (changeP r₀ a₀ i : X → ℂ) (changeP r₁ a₁ i) U) ∧
      EqOn (changeS k₀ r₀ hr₀ a₀ b₀ : X → ℂ) (changeS k₁ r₁ hr₁ a₁ b₁) U := by
  have hp (i) : EqOn (changeP r₀ a₀ i : X → ℂ) (changeP r₁ a₁ i) U := by
    intro x hx
    change (r₀ : X → ℂ) x*(a₀ i : X → ℂ) x=(r₁ : X → ℂ) x*(a₁ i : X → ℂ) x
    rw [hr hx,ha i hx]
  refine ⟨hp,fun x hx => ?_⟩
  simp only [changeS,Subalgebra.coe_smul,Subalgebra.coe_add,Subalgebra.coe_mul,
    smooth_sum_eval,Pi.smul_apply,Pi.add_apply,Pi.mul_apply,smoothInv_apply]
  rw [hk hx,hr hx,hb hx]
  rw [show (∑ i,(logarithmicGrad r₀ hr₀ i : X → ℂ) x*(changeP r₀ a₀ i : X → ℂ) x)=
      ∑ i,(logarithmicGrad r₁ hr₁ i : X → ℂ) x*(changeP r₁ a₁ i : X → ℂ) x from
    Finset.sum_congr rfl (fun i _ => by rw [eqOn_logarithmicGrad hU r₀ r₁ hr₀ hr₁ hr i hx,hp i hx])]
lemma eqOn_transport {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (k₀ k₁ r₀ r₁ : Smooth)
    (hr₀ : ∀ x,(r₀ : X → ℂ) x≠0) (hr₁ : ∀ x,(r₁ : X → ℂ) x≠0)
    (hk₀ : ∀ x,(k₀ : X → ℂ) x≠0) (hk₁ : ∀ x,(k₁ : X → ℂ) x≠0)
    (hl₀ : ∀ x,((k₀+r₀*r₀ : Smooth) : X → ℂ) x≠0)
    (hl₁ : ∀ x,((k₁+r₁*r₁ : Smooth) : X → ℂ) x≠0)
    (hk : EqOn (k₀ : X → ℂ) k₁ U) (hr : EqOn (r₀ : X → ℂ) r₁ U) :
    EqOn (transportT θ k₀ r₀ hk₀ hl₀ : X → ℂ) (transportT θ k₁ r₁ hk₁ hl₁) U ∧
    ∀ i,EqOn (transportQ θ k₀ r₀ hr₀ hk₀ hl₀ i : X → ℂ)
      (transportQ θ k₁ r₁ hr₁ hk₁ hl₁ i) U := by
  have hl : EqOn ((k₀+r₀*r₀ : Smooth) : X → ℂ) (k₁+r₁*r₁ : Smooth) U := by
    intro x hx
    change (k₀ : X → ℂ) x+(r₀ : X → ℂ) x*(r₀ : X → ℂ) x=_
    rw [hk hx,hr hx]
    rfl
  have hγ : EqOn (thetaGamma θ r₀ hr₀ : X → ℂ) (thetaGamma θ r₁ hr₁) U := by
    intro x hx
    simp only [thetaGamma,smooth_sum_eval,Subalgebra.coe_smul,Pi.smul_apply]
    exact Finset.sum_congr rfl (fun i _ => by rw [eqOn_logarithmicGrad hU r₀ r₁ hr₀ hr₁ hr i hx])
  constructor
  · intro x hx
    simp only [transportT,Subalgebra.coe_sub,Subalgebra.coe_mul,Pi.sub_apply,Pi.mul_apply,smoothInv_apply]
    rw [hk hx,hl hx,eqOn_direction hU θ k₀ k₁ hk hx,
      eqOn_direction hU θ (k₀+r₀*r₀) (k₁+r₁*r₁) hl hx]
  · intro i x hx
    simp only [transportQ,Subalgebra.coe_smul,Subalgebra.coe_sub,Subalgebra.coe_mul,
      Pi.smul_apply,Pi.sub_apply,Pi.mul_apply,smoothInv_apply]
    rw [hr hx,hk hx,hl hx,hγ hx,eqOn_direction hU θ k₀ k₁ hk hx,
      eqOn_logarithmicGrad hU r₀ r₁ hr₀ hr₁ hr i hx,
      eqOn_direction hU θ _ _ (eqOn_logarithmicGrad hU r₀ r₁ hr₀ hr₁ hr i) hx]
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators
namespace Elasticity
open ElasticityAugmented ElasticityCGO
open ElasticityCoeffBounds (ExteriorConstant)
lemma null_real_imag (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0) :
    ∃ α β : X,α≠0 ∧ θ=fun i => (α i : ℂ)+Complex.I*(β i : ℂ) := by
  let J := ElasticityParameter.characteristicPlane ElasticityParameter.basis θ
  refine ⟨J 1,J Complex.I,?_,?_⟩
  · intro hh
    have hz : J 1=J 0 := by rw [hh,map_zero]
    exact one_ne_zero (ElasticityParameter.null_plane_injective θ hθ hne hz)
  · funext i
    have ha : J 1 i=(θ i).re := by
      simp only [J,ElasticityParameter.characteristicPlane,add_apply,
        ContinuousLinearMap.smulRight_apply,Complex.reCLM_apply,Complex.imCLM_apply,
        Complex.one_re,Complex.one_im,one_smul,zero_smul,add_zero]
      exact ElasticityParameter.basis_sum_apply _ i
    have hb : J Complex.I i=(θ i).im := by
      simp only [J,ElasticityParameter.characteristicPlane,add_apply,
        ContinuousLinearMap.smulRight_apply,Complex.reCLM_apply,Complex.imCLM_apply,
        Complex.I_re,Complex.I_im,one_smul,zero_smul,zero_add]
      exact ElasticityParameter.basis_sum_apply _ i
    rw [ha,hb,mul_comm]
    exact (Complex.re_add_im (θ i)).symm

/-- The DN-derived common physical frame in the exact normal variables.
All coefficients and the exterior identification are still the actual Lamé pair. -/
theorem dn_common_normal_frame {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
    (r₀ : ℝ) (hr₀ : 1≤r₀) (hK : closure Ω⊆Metric.closedBall 0 r₀)
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) :
    let k := fun q => smoothOfReal (lam q) (hl q)+smoothOfReal (m q) (hm q)
    let r := fun q => positiveRoot (m q) (hm q) (fun x => (hp q x).1)
    let hr := fun q => positiveRoot_nonzero (m q) (hm q) (fun x => (hp q x).1)
    ∃ hk : ∀ q x,(k q : X → ℂ) x≠0,
    ∃ hL : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0,
    ∃ p : Fin 2 → Fin 3 → Fin 3 → Smooth,∃ s : Fin 2 → Fin 3 → Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ q ν,normal θ (p q ν)=0) ∧
      (∀ q ν x,x∈Metric.ball 0 (r₀+3) →
        (∀ i,(direction (A := Smooth) coord θ (p q ν i) : X → ℂ) x=θ i*(s q ν : X → ℂ) x) ∧
        (direction (A := Smooth) coord θ (s q ν) : X → ℂ) x=
          ((transportT θ (k q) (r q) (hk q) (hL q)*s q ν+
            ∑ i,transportQ θ (k q) (r q) (hr q) (hk q) (hL q) i*p q ν i : Smooth) : X → ℂ) x) ∧
      (∀ ν x,x∉closure Ω → (∀ i,(p 0 ν i : X → ℂ) x=(p 1 ν i : X → ℂ) x) ∧
        (s 0 ν : X → ℂ) x=(s 1 ν : X → ℂ) x) ∧
      ∀ ν x,((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (p 0 ν i : X → ℂ) x),(s 0 ν : X → ℂ) x) := by
  intro k r hr
  obtain ⟨α,β,hα,hαβ⟩ := null_real_imag θ hθ hne
  have heq (i) := congrFun hαβ i
  have hθ' : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0 := by
    simpa only [← heq] using hθ
  have hh := dn_common_leading_frame hΩ hOB r₀ hr₀ hK α β hα hθ' lam m hl hm hp hcll hclm he hDN
  dsimp only at hh
  rw [← hαβ] at hh
  obtain ⟨a,B,hn,hR,hS,hs,hB⟩ := hh
  have hr2 (q) : r q*r q=smoothOfReal (m q) (hm q) := positiveRoot_square _ _ _
  have hk : ∀ q x,(k q : X → ℂ) x≠0 := by
    intro q x
    change (lam q x : ℂ)+(m q x : ℂ)≠0
    exact_mod_cast (real_k_positive (lam q) (m q) (hp q) x).ne'
  have hL : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0 := by
    intro q x
    rw [hr2]
    change (lam q x : ℂ)+(m q x : ℂ)+(m q x : ℂ)≠0
    exact_mod_cast (real_longitudinal_positive (lam q) (m q) (hp q) x).ne'
  let p := fun q ν => changeP (r q) (a q ν).1
  let s := fun q ν => changeS (k q) (r q) (hr q) (a q ν).1 (a q ν).2
  refine ⟨hk,hL,p,s,B,?_,?_,?_,hB⟩
  · intro q ν
    have heq : normal θ (p q ν)=r q*normal θ (a q ν).1 := by
      simp only [p,normal,changeP,Algebra.smul_def,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [heq,hn,mul_zero]
  · intro q ν x hx
    apply (leading_equations_at_iff θ (k q) (r q) (hr q) (hk q) (hL q) (a q ν).1 (a q ν).2 x).mp
    simpa only [hr2,k,add_sub_cancel_right] using ⟨fun i => hR q ν i hx,hS q ν hx⟩
  · intro ν x hx
    have hkE : EqOn (k 0 : X → ℂ) (k 1) (closure Ω)ᶜ := by
      intro y hy
      have hy' : y∉Ω := fun hyΩ => hy (subset_closure hyΩ)
      change (lam 0 y : ℂ)+(m 0 y : ℂ)=(lam 1 y : ℂ)+(m 1 y : ℂ)
      rw [(he y hy').1,(he y hy').2]
    have hrE : EqOn (r 0 : X → ℂ) (r 1) (closure Ω)ᶜ := by
      intro y hy
      change (Real.sqrt (m 0 y) : ℂ)=(Real.sqrt (m 1 y) : ℂ)
      rw [(he y (fun hyΩ => hy (subset_closure hyΩ))).2]
    have haE (i : Fin 4) : EqOn
        (((Fin.cons (a 0 ν).2 (a 0 ν).1 : Fin 4 → Smooth) i) : X → ℂ)
        ((Fin.cons (a 1 ν).2 (a 1 ν).1 : Fin 4 → Smooth) i) (closure Ω)ᶜ := by
      intro y hy
      have hz := image_eq_zero_of_notMem_tsupport (fun hh => hy (hs ν i hh))
      exact (sub_eq_zero.mp hz).symm
    have hc := eqOn_physical_change isClosed_closure.isOpen_compl (k 0) (k 1) (r 0) (r 1)
      (hr 0) (hr 1) (a 0 ν).1 (a 1 ν).1 (a 0 ν).2 (a 1 ν).2 hkE hrE
      (fun i => haE i.succ) (haE 0)
    exact ⟨fun i => hc.1 i hx,hc.2 hx⟩
end Elasticity

end
end

end OAI
