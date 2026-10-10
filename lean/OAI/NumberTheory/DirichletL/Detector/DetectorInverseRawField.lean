import OAI.NumberTheory.DirichletL.Dictionary.InverseRawReference
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawUniform
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
import OAI.NumberTheory.DirichletL.Detector.DetectorMomentData

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.ProbeDetectorInverseRawField
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open HeckeDetectorInverseFiberCount DetectorDictionaryInverseClippedUniform
open ProbeHighRowFamily ProbeFinalAssembly

private theorem raw_mono (data:RowData)(W:ℝ→ℂ)(c κ A B:ℝ)
    (hAB:A≤B)(h:RawMoment data W c κ A):RawMoment data W c κ B:=by
  intro H D hH hD hcap rows hrows
  apply (h H D hH hD hcap rows hrows).trans
  gcongr

theorem fixed_raw_profiles (c κ:ℝ)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C:ℝ,0<C ∧
      ∀reverse:Bool,∀n:ℕ,n≤2→∀U:ℝ,0<U→∀tstar r:ℝ,
      ∀s∈Set.Icc (0:ℝ) 1,∀height t:ℝ,0≤height→t∈Set.Icc (-height) height→
      let W:=twistProfile (logTest (orientedProfile reverse (inverseTest U tstar r)) n) s t;
      RawMoment data W c κ (C*(1+height)^J) ∧
      RawMoment data (scaleProfile W) c κ (C*(1+height)^J):=by
  obtain ⟨J,hreference⟩:=DetectorDictionaryInverseRawReference.raw_reference_moment
    referenceWindow (1/18) (13/4) c κ (by norm_num) (by norm_num)
    (fun x hx=>referenceWindow_support (subset_tsupport _ hx)) hc hκ
  obtain ⟨K,C,hC,hfamily⟩:=DetectorDictionaryInverseRawUniform.raw_pair_height_uniform J
  refine ⟨K,?_⟩
  intro data
  obtain ⟨A,hA,href⟩:=hreference data
  exact ⟨A*C,mul_pos hA hC,hfamily data c κ A hA.le href⟩

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

theorem source_batch_inverse_raw
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(εm:ℝ)(counts:CountParameters M H εm):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧
    ∀{Slot:Type*}{U a ε tstar T allowance:ℝ}{i:ℕ},0<U→
    ∀(B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S hS η→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height→∀n:ℕ,n≤2→∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J):=by
  obtain ⟨JB,hB⟩:=fixed_raw_profiles counts.cB counts.kB counts.cB_pos counts.kB_pos
  obtain ⟨JH,hHraw⟩:=fixed_raw_profiles counts.cH counts.kH counts.cH_pos counts.kH_pos
  refine ⟨JB+JH,?_⟩
  intro η
  let data:=sourceMomentData M H hH S hS η
  choose CB hCB hb using (fun label=>hB (data label))
  choose CH hCH hh using (fun label=>hHraw (data label))
  let C:ℝ:=1+(∑label,CB label)+(∑label,CH label)
  have hsumB:0≤∑label,CB label:=Finset.sum_nonneg (fun j _=>(hCB j).le)
  have hsumH:0≤∑label,CH label:=Finset.sum_nonneg (fun j _=>(hCH j).le)
  have hC:0<C:=by dsimp [C];linarith
  have hCBound (label):CB label≤C:=by
    have he:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hCB j).le) (Finset.mem_univ label)
    dsimp [C];linarith
  have hCHound (label):CH label≤C:=by
    have he:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hCH j).le) (Finset.mem_univ label)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro Slot U a ε tstar T allowance i hU B hdata bin label left right hne height hheight n hn s hs t ht F W
  have hd:F.rowData=data label:=by
    change B.data label=data label
    rw [hdata]
  have hbase:1≤1+height:=by linarith
  by_cases hbranch:2*a-1≤5/6
  · simp only [hbranch,ite_true]
    have hpair:=hb label F.reverse n hn U hU tstar F.r s hs height t hheight ht
    have hconstant:CB label*(1+height)^JB≤C*(1+height)^(JB+JH):=
      mul_le_mul (hCBound label) (pow_le_pow_right₀ hbase (Nat.le_add_right _ _))
        (by positivity) hC.le
    rw [hd]
    exact ⟨raw_mono _ _ _ _ _ _ hconstant hpair.1,raw_mono _ _ _ _ _ _ hconstant hpair.2⟩
  · simp only [hbranch,ite_false]
    have hpair:=hh label F.reverse n hn U hU tstar F.r s hs height t hheight ht
    have hconstant:CH label*(1+height)^JH≤C*(1+height)^(JB+JH):=
      mul_le_mul (hCHound label) (pow_le_pow_right₀ hbase (Nat.le_add_left _ _))
        (by positivity) hC.le
    rw [hd]
    exact ⟨raw_mono _ _ _ _ _ _ hconstant hpair.1,raw_mono _ _ _ _ _ _ hconstant hpair.2⟩

end SevenEighths.ProbeDetectorInverseRawField

end

end OAI
