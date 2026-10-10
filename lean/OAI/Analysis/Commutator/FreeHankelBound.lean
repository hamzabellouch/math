import Mathlib
import OAI.Analysis.Commutator.FiniteHankel
import OAI.Analysis.Commutator.FreeDihedralColumns
import OAI.Analysis.Commutator.FreeFejerNorm
import OAI.Analysis.Commutator.FreeHankelEntries

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

local notation "CE" => Completion (factorSpace t S true)

lemma concrete_hankel_assembly
    (N : ℕ) (hN : 0 < N) (U : Fin N → CE →ₗᵢ[ℂ] t.functional.GNS)
    (horth : ∀ i j, i ≠ j → ∀ x y : CE, inner ℂ (U i x) (U j y) = 0)
    (G L : t.functional.GNS →L[ℂ] t.functional.GNS) (B Q : CE →L[ℂ] CE) (u c ε : ℝ)
    (hu : 0 < u) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hL : ‖L‖ ≤ 4*u)
    (hG : ‖G*L-L*G‖ ≤ ε*‖L‖)
    (hR : ∀ i, ‖G.comp (U i).toContinuousLinearMap -
      (U i).toContinuousLinearMap.comp B‖ ≤ 2*c*ε)
    (hR' : ∀ i, ‖(ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=t.functional.GNS) (F:=t.functional.GNS) G).comp (U i).toContinuousLinearMap -
      (U i).toContinuousLinearMap.comp (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=CE) (F:=CE) B)‖ ≤ 2*c*ε)
    (hRorth : ∀ i j, i ≠ j → ∀ x : CE,
      inner ℂ (G (U i x) - U i (B x)) (G (U j x) - U j (B x)) = 0)
    (hRorth' : ∀ i j, i ≠ j → ∀ x : CE,
      inner ℂ ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=t.functional.GNS) (F:=t.functional.GNS) G) (U i x) - U i ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=CE) (F:=CE) B) x))
        ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=t.functional.GNS) (F:=t.functional.GNS) G) (U j x) - U j ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=CE) (F:=CE) B) x)) = 0)
    (a : Fin N → Fin N → ℂ)
    (hentry : ∀ i j, ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=CE) (F:=t.functional.GNS) (U i).toContinuousLinearMap).comp L).comp
      (U j).toContinuousLinearMap = (u : ℂ) • (a i j • 1 +
        (Complex.ofReal (((2*N : ℝ) - i.val - j.val - 1)/(2*N : ℝ)^2)) • Q)) :
    ‖B*Q-Q*B‖ ≤ 16*(1+4*c)*ε := by
  exact @FiniteHankel.norm_commutator_le_of_finite_entries
    t.functional.GNS (Completion (factorSpace t S true))
    (inferInstanceAs (NormedAddCommGroup t.functional.GNS))
    (inferInstanceAs (InnerProductSpace ℂ t.functional.GNS))
    (inferInstanceAs (CompleteSpace t.functional.GNS))
    (inferInstanceAs (NormedAddCommGroup (Completion (factorSpace t S true))))
    (inferInstanceAs (InnerProductSpace ℂ (Completion (factorSpace t S true))))
    (inferInstanceAs (CompleteSpace (Completion (factorSpace t S true))))
    N hN U horth G L B Q u c ε hu hc hε hL hG hR hR' hRorth hRorth' a hentry

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S false=f.range)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hrot : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)
local notation "sl" => (letterOf t S true (s:A) hs hs0)
local notation "sn" => (norm_letterOf_unitary t S true s hs hs0)
local notation "dl" => (letterOf t S false (d:A) hd hd0)
local notation "dn" => (norm_letterOf_unitary t S false d hd hd0)

include htr hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp hpD in
lemma normalized_fejer_entry (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (N : ℕ) (hN : 0 < N) (i j : Fin N) :
    ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=Completion (factorSpace t S true)) (F:=t.functional.GNS)
      (normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr i.val).toContinuousLinearMap).comp
      (t.functional.gnsStarAlgHom ((e:A)*((fejerCorner hp (d*s) (2*N):Corner hp):A)*(e:A)))).comp
      (normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr j.val).toContinuousLinearMap =
    ((halfCornerTrace hp t.functional.toLinearMap e).re:ℂ) •
      ((2*t.functional (wave (d*s) ((i.val:ℤ)-j.val)*
        ((fejerCorner hp (d*s) (2*N):Corner hp):A))) •
          (1:Completion (factorSpace t S true) →L[ℂ] Completion (factorSpace t S true))+
       (Complex.ofReal (((2*N:ℝ)-i.val-j.val-1)/(2*N:ℝ)^2)) • baseAction t S hfree (s:A)) := by
  rw [normalizedColumn_eq_dihedral t S hfree f hf hS d s hd hs hd0 hs0 hd2 hs2 e0 hr,
    normalizedColumn_eq_dihedral t S hfree f hf hS d s hd hs hd0 hs0 hd2 hs2 e0 hr,heq]
  exact finite_fejer_entry t S hfree f hf hp htr d s hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp hpD
    e0 e heq heproj he hr N hN i j

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S true n →L[ℂ] multiplicityLevel t S true n)

variable (hB : ∀ n a (x : letterSpace t S false) v,
  G (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n v)=
    repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n (B n v))

variable (hB' : ∀ n a (x : letterSpace t S false) v,
  G.adjoint (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n v)=
    repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n
      ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) v))

include hB hB' in
lemma normalized_errors (e0 : D)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (N : ℕ) (δ : ℝ) (hδ : 0≤δ)
    (hprop : ∀ n v, ‖B n (repeatInsertion t S sl sn n v)-
      repeatInsertion t S sl sn n (B 0 v)‖≤δ*‖v‖)
    (hprop' : ∀ n v,
      ‖(ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) (repeatInsertion t S sl sn n v)-
      repeatInsertion t S sl sn n
        ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true 0)
          (F:=multiplicityLevel t S true 0) (B 0)) v)‖≤δ*‖v‖) :
    let E := Completion (factorSpace t S true)
    let U : Fin N → E →ₗᵢ[ℂ] t.functional.GNS := fun i =>
      normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr i.val
    (∀ i : Fin N, ‖G.comp (U i).toContinuousLinearMap-
      (U i).toContinuousLinearMap.comp (B 0)‖≤δ) ∧
    (∀ i : Fin N, ‖G.adjoint.comp (U i).toContinuousLinearMap-
      (U i).toContinuousLinearMap.comp
        (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0))‖≤δ) ∧
    (∀ i j : Fin N, i≠j → ∀ x : E,
      inner ℂ (G (U i x)-U i (B 0 x)) (G (U j x)-U j (B 0 x))=0) ∧
    (∀ i j : Fin N, i≠j → ∀ x : E,
      inner ℂ (G.adjoint (U i x)-U i ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0)) x))
        (G.adjoint (U j x)-U j ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0)) x))=0) := by
  dsimp only
  let E := Completion (factorSpace t S true)
  let U : Fin N → E →ₗᵢ[ℂ] t.functional.GNS := fun i =>
    normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr i.val
  have hR : ∀ i : Fin N, ‖G.comp (U i).toContinuousLinearMap-
      (U i).toContinuousLinearMap.comp (B 0)‖≤δ := by
    intro i
    exact norm_normalizedColumn_error_le t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr
      G B hB _ hδ i.val (hprop i.val)
  have hR' : ∀ i : Fin N, ‖G.adjoint.comp (U i).toContinuousLinearMap-
      (U i).toContinuousLinearMap.comp
        (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0))‖≤δ := by
    intro i
    exact norm_normalizedColumn_error_le t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr
      G.adjoint (fun n => ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) hB' _ hδ i.val (hprop' i.val)
  have hRorth : ∀ i j : Fin N, i≠j → ∀ x : E,
      inner ℂ (G (U i x)-U i (B 0 x)) (G (U j x)-U j (B 0 x))=0 := by
    intro i j hij x
    exact normalizedColumn_error_orthogonal t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr
      G B hB (mt Fin.ext hij) x x
  have hRorth' : ∀ i j : Fin N, i≠j → ∀ x : E,
      inner ℂ (G.adjoint (U i x)-U i ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0)) x))
        (G.adjoint (U j x)-U j ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0)) x))=0 := by
    intro i j hij x
    exact normalizedColumn_error_orthogonal t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr
      G.adjoint (fun n => ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) hB' (mt Fin.ext hij) x x
  exact ⟨hR,hR',hRorth,hRorth'⟩

include htr hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp hpD hB hB' in
theorem free_hankel_bound (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (c ε : ℝ) (hc : 0≤c) (hε : 0≤ε)
    (hsmall : ∀ a : A, (e:A)*a*(e:A)=a →
      ‖G*t.functional.gnsStarAlgHom a-t.functional.gnsStarAlgHom a*G‖≤ε*‖a‖)
    (hprop : ∀ n v, ‖B n (repeatInsertion t S sl sn n v)-
      repeatInsertion t S sl sn n (B 0 v)‖≤(2*c*ε)*‖v‖)
    (hprop' : ∀ n v,
      ‖(ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) (repeatInsertion t S sl sn n v)-
      repeatInsertion t S sl sn n
        ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true 0)
          (F:=multiplicityLevel t S true 0) (B 0)) v)‖≤(2*c*ε)*‖v‖) :
    ‖B 0*baseAction t S hfree (s:A)-baseAction t S hfree (s:A)*B 0‖≤16*(1+4*c)*ε := by
  let E := Completion (factorSpace t S true)
  let u : ℝ := (halfCornerTrace hp t.functional.toLinearMap e).re
  have hu : 0<u := by
    dsimp only [u]
    rw [halfCornerTrace_normalization_re t f hf hp e0 e heq heproj]
    positivity
  obtain ⟨N,hNsize⟩ := exists_nat_gt (4/u)
  have hN : 0 < N := by
    have : (0:ℝ)<N := lt_trans (div_pos (by norm_num) hu) hNsize
    exact_mod_cast this
  have hsize : 8≤((2*N:ℕ):ℝ)*u := by
    have hh := (div_lt_iff₀ hu).mp hNsize
    push_cast
    nlinarith
  let U : Fin N → E →ₗᵢ[ℂ] t.functional.GNS := fun i =>
    normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr i.val
  let L := t.functional.gnsStarAlgHom ((e:A)*((fejerCorner hp (d*s) (2*N):Corner hp):A)*(e:A))
  have horth : ∀ i j : Fin N, i≠j → ∀ x y : E, inner ℂ (U i x) (U j y)=0 := by
    intro i j hij x y
    exact normalizedColumn_orthogonal t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr
      (mt Fin.ext hij) x y
  have hL : ‖L‖≤4*u := free_fejer_gns_norm t S hfree htr d s hd hs hd0 hs0 hrot hd2
    hp hpform hpd hdp hpD e heproj he (2*N) (by omega) hsize
  have hG : ‖G*L-L*G‖≤ε*‖L‖ := by
    dsimp only [L]
    rw [FreeCreation.norm_gns]
    exact hsmall _ (sandwich_supported hp e (fejerCorner hp (d*s) (2*N)) heproj)
  obtain ⟨hR,hR',hRorth,hRorth'⟩ := normalized_errors t S hfree f hf hS d s hd hs hd0 hs0
    G B hB hB' e0 hr N (2*c*ε) (by positivity) hprop hprop'
  let a : Fin N → Fin N → ℂ := fun i j => 2*t.functional
    (wave (d*s) ((i.val:ℤ)-j.val)*((fejerCorner hp (d*s) (2*N):Corner hp):A))
  have hentry : ∀ i j : Fin N, ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=t.functional.GNS)
      (U i).toContinuousLinearMap).comp L).comp
      (U j).toContinuousLinearMap=(u:ℂ) • (a i j • (1:E→L[ℂ]E)+
        Complex.ofReal (((2*N:ℝ)-i.val-j.val-1)/(2*N:ℝ)^2) • baseAction t S hfree (s:A)) := by
    intro i j
    exact normalized_fejer_entry t S hfree f hf hS htr d s hd hs hd0 hs0 hrot hd2 hs2
      hp hpform hpd hdp hpD e0 e heq heproj he hr N hN i j
  have hfinal := concrete_hankel_assembly t S
    N hN U horth G L (B 0) (baseAction t S hfree (s:A)) u c ε hu hc hε
    hL hG hR hR' hRorth hRorth' a hentry
  exact hfinal

end Kadison.FreeBlocks

end

end
end

end OAI
