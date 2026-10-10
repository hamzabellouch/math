import OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMass

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma support_family_card {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (S : Finset (Finset ι)) (U : ℝ) (hU : 0<U) (hS : ∀A∈S,primeProductNorm p A≤U) :
    (S.card:ℝ)≤128*U := by
  by_cases h1 : 1≤U
  · have hh := DescentFiberCost.finite_ideal_count_real (S.image (sourceIdeal p)) U h1
      (by intro I hI;obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hI;exact sourceIdeal_ne_zero p hp A)
      (by
        intro I hI
        obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hI
        simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hS A hA)
    simpa only [Finset.card_image_of_injective S (sourceIdeal_injective p hinj)] using hh

  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      exact h1 ((primeProductNorm_ge_one p hp A).trans (hS A hA))
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem original_source_card (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(B H V T : ℝ),
    1≤B → 0≤H → 0<V → 0<T → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤H) →
    (∀x∈S,primeProductNorm p x.firstCommon≤V) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤T) →
    (S.card:ℝ)≤C*B^(1+eps)*H*V*T*(B^2*V*T)^eps := by
  obtain ⟨Cf,hCf,hfiber⟩ := core_fiber_small_power Jmax eps heps
  obtain ⟨Cb,hCb,hcube⟩ := cube_coordinates_parity_count eps heps
  refine ⟨Cf*Cb*128^2,by positivity,?_⟩
  intro ι _ p hp _ hinj Jo hJo S B H V T hB hH hV hT hS hleft hright hactive hcommon hquot
  let Q := S.image core
  let bs := S.image Source.cube
  let cs := S.image Source.firstCommon
  let ts := S.image Source.quotientSupport
  have hbcount : (bs.card:ℝ)≤Cb*B^(1+eps)*H := hcube p hp hinj bs B H hB hH
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact (hS x hx).admissible)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hleft x hx)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hright x hx)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hactive x hx)
  have hccount : (cs.card:ℝ)≤128*V := support_family_card p hp hinj cs V hV
    (by intro A hA;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA;exact hcommon x hx)
  have htcount : (ts.card:ℝ)≤128*T := support_family_card p hp hinj ts T hT
    (by intro A hA;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA;exact hquot x hx)
  have hsub : Q⊆bs×ˢ(cs×ˢts) := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,Finset.mem_image_of_mem _ hx⟩⟩
  have hQcard : (Q.card:ℝ)≤(Cb*B^(1+eps)*H)*(128*V)*(128*T) := by
    have hh : (Q.card:ℝ)≤(bs.card:ℝ)*((cs.card:ℝ)*(ts.card:ℝ)) := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (by simp only [Finset.card_product])
    apply hh.trans
    calc
      _ ≤ (Cb*B^(1+eps)*H)*((128*V)*(128*T)) := by gcongr
      _ = _ := by ring
  have hF (q : Core ι) (hq : q∈Q) :
      ((S.filter (fun x=>core x=q)).card:ℝ)≤Cf*(B^2*V*T)^eps := by
    have hf := hfiber p hp hinj Jo hJo (S.filter (fun x=>core x=q)) q
      (fun x hx=>hS x (Finset.mem_filter.mp hx).1) (fun x hx=>(Finset.mem_filter.mp hx).2)
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    apply hf.trans
    apply mul_le_mul_of_nonneg_left _ hCf.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (divisorTarget_norm_bound p hp (core x) B V T (zero_le_one.trans hB) hV.le hT.le
        (hleft x hx) (hright x hx) (hcommon x hx) (hquot x hx)) heps.le
  have he : (S.card:ℝ)=∑q∈Q,((S.filter (fun x=>core x=q)).card:ℝ) := by
    calc
      _ = ∑_x∈S,(1:ℝ) := by simp
      _ = ∑q∈Q,∑_x∈S.filter (fun x=>core x=q),(1:ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx=>Finset.mem_image_of_mem core hx) _).symm
      _ = _ := by simp
  rw [he]
  calc
    _ ≤ ∑_q∈Q,Cf*(B^2*V*T)^eps := Finset.sum_le_sum hF
    _ = (Q.card:ℝ)*(Cf*(B^2*V*T)^eps) := by simp
    _ ≤ ((Cb*B^(1+eps)*H)*(128*V)*(128*T))*(Cf*(B^2*V*T)^eps) :=
      mul_le_mul_of_nonneg_right hQcard (by positivity)
    _ = _ := by ring

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
