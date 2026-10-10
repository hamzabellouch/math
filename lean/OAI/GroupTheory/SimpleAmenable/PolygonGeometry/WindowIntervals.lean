import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SectorControl

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WindowIntervals

@[simp] theorem coordinateShift_sub (j : Fin 2) (u v : CutRing) :
    coordinateShift j (u-v) = coordinateShift j u-coordinateShift j v := by
  rw [sub_eq_add_neg,coordinateShift_add,coordinateShift_neg,sub_eq_add_neg]

theorem coordinateBetween_reverse {a : ℕ} (j : Fin 2) (u v : CutRing)
    (h : Int.fract (ordinary (v-u)) ≠ 0) :
    coordinateBetween a j v u = (coordinateBetween a j u v)ᶜ := by
  unfold coordinateBetween
  rw [show u-v = -(v-u) by ring,coordinateArc_neg j (v-u) h,Set.preimage_compl]
  congr 1
  ext p
  simp only [Set.mem_preimage]
  rw [← translate_add]
  rw [coordinateShift_sub]
  abel_nf

theorem coordinateBetween_empty {a : ℕ} (j : Fin 2) (u v : CutRing)
    (h : Int.fract (ordinary (v-u)) = 0) : coordinateBetween a j u v = ∅ := by
  rw [coordinateBetween,coordinateArc_zero_of_fract j _ h,Set.preimage_empty]

theorem coordinate_window_between_resolved_all {a : ℕ} {r : CutRing}
    (n : ℕ) (q : Fin 2 → ℤ) (j : Fin 2) (i k : ℕ) (hi : i < n) (hk : k < n) :
    coordinateBetween a j (((q j+(i:ℤ)):CutRing)*cutTau)
      (((q j+(k:ℤ)):CutRing)*cutTau) ∈ resolvedAlgebra
        (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
          (coordinateWindowPrimitives n q) z).val) := by
  by_cases hik : i ≤ k
  · exact coordinate_window_between_resolved n q j i k hik hk
  · let u : CutRing := ((q j+(i:ℤ)):CutRing)*cutTau
    let v : CutRing := ((q j+(k:ℤ)):CutRing)*cutTau
    by_cases h : Int.fract (ordinary (v-u)) = 0
    · rw [coordinateBetween_empty j u v h]
      exact BooleanSubalgebra.bot_mem
    · have hr := coordinateBetween_reverse (a := a) j u v h
      have hh := coordinate_window_between_resolved (a := a) (r := r) n q j k i (by omega) hi
      rw [hr] at hh
      simpa only [compl_compl] using BooleanSubalgebra.compl_mem hh

theorem coordinateBetween_period {a : ℕ} (j : Fin 2) (u v : CutRing) (p q : ℤ) :
    coordinateBetween a j (u+p) (v+q) = coordinateBetween a j u v := by
  unfold coordinateBetween
  have he : coordinateArc a j (v+q-(u+p)) = coordinateArc a j (v-u) := by
    ext x
    simp only [coordinateArc,Set.mem_ofPred_eq,map_sub,map_add,map_intCast]
    rw [show ordinary v+(q:ℝ)-(ordinary u+(p:ℝ)) = ordinary v-ordinary u+((q-p:ℤ):ℝ) by push_cast; ring]
    rw [Int.fract_add_intCast]
  rw [he]
  ext x
  simp only [Set.mem_preimage]
  have ht : translate a (-coordinateShift j (u+p)) x = translate a (-coordinateShift j u) x := by
    change translation a (-coordinateShift j (u+p)) x = translation a (-coordinateShift j u) x
    fin_cases j
    · have hp := DFunLike.congr_fun (translation_period a (-u,0) (-p,0)) x
      simpa [coordinateShift,add_comm] using hp
    · have hp := DFunLike.congr_fun (translation_period a (0,-u) (0,-p)) x
      simpa [coordinateShift,add_comm] using hp
  rw [ht]

theorem coordinateLabelWindow_resolved {a : ℕ} {r : CutRing}
    (n : ℕ) (q : Fin 2 → ℤ) (j : Fin 2) (u v : CutRing)
    (hu : q j ≤ endpointLabel u ∧ endpointLabel u < q j+n)
    (hv : q j ≤ endpointLabel v ∧ endpointLabel v < q j+n) :
    coordinateBetween a j u v ∈ resolvedAlgebra
      (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (coordinateWindowPrimitives n q) z).val) := by
  let i := (endpointLabel u-q j).toNat
  let k := (endpointLabel v-q j).toNat
  have hi : (i:ℤ) = endpointLabel u-q j := Int.toNat_of_nonneg (by omega)
  have hk : (k:ℤ) = endpointLabel v-q j := Int.toNat_of_nonneg (by omega)
  have hi' : i < n := by omega
  have hk' : k < n := by omega
  have hu' : u = (((q j+(i:ℤ)):CutRing)*cutTau)+(u.re:CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [cutTau,hi,endpointLabel]
  have hv' : v = (((q j+(k:ℤ)):CutRing)*cutTau)+(v.re:CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [cutTau,hk,endpointLabel]
  rw [hu',hv',coordinateBetween_period]
  exact coordinate_window_between_resolved_all n q j i k hi' hk'

end WindowIntervals

section EnlargedControl

namespace SameActionOn
variable {E H : Type*} [Group H] {f g : E → H} {P Q : Subgroup H}

theorem mono (h : SameActionOn f g Q) (hPQ : P ≤ Q) : SameActionOn f g P :=
  fun s x hx => h s x (hPQ hx)

theorem comp {F : Type*} (h : SameActionOn f g P) (v : F → E) :
    SameActionOn (f ∘ v) (g ∘ v) P := fun s x hx => h (v s) x hx

end SameActionOn

theorem alphabetPerfect {α : Type*} [Fintype α] [DecidableEq α]
    (J : Finset α) (hJ : 5 ≤ J.card) : Group.IsPerfect (alternatingGroup J) :=
  ⟨commutator_alternatingGroup_eq_top (by simpa using hJ)⟩

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]

theorem initialAlphabet_zero (I : Finset (Fin (m+1))) :
    B.initialAlphabet I 0 = B.c.comp (subtypeAlternatingHom I) := by
  rw [initialAlphabet,B.initialConditional_zero]

theorem geometricSector_control_enlarged
    {I J : Finset (Fin (m+1))} [Group.IsPerfect (alternatingGroup I)]
    [Group.IsPerfect (alternatingGroup J)] (hIJ : I ⊆ J)
    (b c : Fin (m+1)) (hb : b ∉ I) (hc : c ∉ J)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (g : B.PrimitiveFamilyLaw J c hc P)
    (V W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hVW : V ≤ W) :
    SameActionOn (B.geometricSector J c hc P g W)
      ((B.c.comp (subtypeAlternatingHom J)).comp (universalProjection (alternatingGroup J)))
      (B.geometricSector I b hb P h V).range := by
  rw [← B.initialAlphabet_zero J]
  apply SameActionOn.mono (B.geometricSector_control J c hc P g V W hVW)
  rintro x ⟨s,rfl⟩
  refine ⟨universalMap (subalphabetHom hIJ) s,?_⟩
  exact DFunLike.congr_fun (B.geometricSector_inclusion hIJ b c hb hc P h g V hV) s

theorem geometricSector_conditional_move
    {I J : Finset (Fin (m+1))} [Group.IsPerfect (alternatingGroup I)]
    [Group.IsPerfect (alternatingGroup J)] (hIJ : I ⊆ J)
    (b c : Fin (m+1)) (hb : b ∉ I) (hc : c ∉ J)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (g : B.PrimitiveFamilyLaw J c hc P)
    (V W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hVW : V ≤ W) (σ : alternatingGroup (Fin (m+1))) (hσ : σ.val.support ⊆ J) :
    ∃ v ∈ (B.geometricSector J c hc P g W).range,
      v ∈ sourceAlignedGroup a r m hm M B.t J ∧
      ∀ x ∈ (B.geometricSector I b hb P h V).range,
        v*x*v⁻¹ = B.c σ*x*(B.c σ)⁻¹ := by
  obtain ⟨s,hs⟩ := (subtypeAlternatingHom_mem_range J σ).mpr hσ
  obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup J) s
  refine ⟨B.geometricSector J c hc P g W t,⟨t,rfl⟩,
    B.geometricSector_aligned J c hc P g W t,?_⟩
  intro x hx
  have hh := B.geometricSector_control_enlarged hIJ b c hb hc P h g V W hV hVW t x hx
  simpa only [MonoidHom.comp_apply,ht,hs] using hh

end InitialCoverSystem
end EnlargedControl

end SimpleAmenable
end
end

end OAI
