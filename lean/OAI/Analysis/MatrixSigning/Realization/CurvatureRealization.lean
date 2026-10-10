import Mathlib
import OAI.Analysis.MatrixSigning.Realization.StencilRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def squareSumData (v : List ℚ) : ℚ := (v.map (fun q => q^2)).sum
def squareSum : Realizes vectorCode ratCode squareSumData := (identity ratCode).pow 2 |>.map.then sumRationals
lemma squareSum_data {n : ℕ} (v : Fin n → ℚ) : squareSumData (List.ofFn v)=RationalRoot.sqSum v := by
  simp [squareSumData,RationalRoot.sqSum,List.sum_ofFn,Function.comp_def]

def vectorDivide : Realizes (prodCode ratCode vectorCode) vectorCode
    (fun p => p.2.map (fun x => x/p.1)) :=
  ((second ratCode ratCode).div (first ratCode ratCode)).mapCtx

def initialScaleData (v : List ℚ) := v.map (fun x => x/(1+squareSumData v))
def initialScale : Realizes vectorCode vectorCode initialScaleData :=
  (((constant vectorCode ratCode 1).add squareSum).both (identity vectorCode)).then vectorDivide
lemma initialScale_data {n : ℕ} (v : Fin n → ℚ) :
    initialScaleData (List.ofFn v)=List.ofFn (RationalRoot.initialScale v) := by
  simp only [initialScaleData,squareSum_data,List.map_ofFn,Function.comp_def]
  rfl

def normalizeData (p : ℚ×List ℚ) : List ℚ :=
  let u := initialScaleData p.2
  u.map (fun t => t/RationalRoot.upperSqrt (squareSumData u) (p.1*squareSumData u))
def normalizeVector : Realizes (prodCode ratCode vectorCode) vectorCode normalizeData :=
  let beta := first ratCode vectorCode
  let u := (second ratCode vectorCode).then initialScale
  let ss := u.then squareSum
  ((((ss.both (beta.mul ss)).then upperSqrt).both u).then vectorDivide)
lemma normalize_data {n : ℕ} (beta : ℚ) (v : Fin n → ℚ) :
    normalizeData (beta,List.ofFn v)=List.ofFn (fun i => RationalRoot.normalize v beta i) := by
  simp only [normalizeData,initialScale_data,squareSum_data,List.map_ofFn,Function.comp_def,RationalRoot.normalize]

def intCeil : Realizes ratCode ratCode (fun q => (⌈q⌉ : ℚ)) :=
  (((identity ratCode).neg.then ratFloor).neg).congr (by intro q;simp [Int.floor_neg])
def nearest : Realizes ratCode ratCode (fun q => (RationalRoot.nearest q : ℚ)) :=
  let t := identity ratCode
  let half := constant ratCode ratCode (1/2)
  (((constant ratCode ratCode 0).le t).ite ((t.sub half).then intCeil)
    (((t.neg.sub half).then intCeil).neg)).congr (by
      intro q;simp only [RationalRoot.nearest,decide_eq_true_eq,id_eq];split_ifs <;> simp)
def nearestMesh : Realizes (prodCode ratCode ratCode) ratCode
    (fun p => p.1*(RationalRoot.nearest (p.2/p.1) : ℚ)) :=
  let rho := first ratCode ratCode
  rho.mul (((second ratCode ratCode).div rho).then nearest)
def roundMesh := nearestMesh.mapCtx
lemma roundMesh_data {n : ℕ} (rho : ℚ) (v : Fin n → ℚ) :
    (List.ofFn v).map (fun x => rho*(RationalRoot.nearest (x/rho):ℚ))=
      List.ofFn (RationalRoot.roundMesh rho v) := by
    rw [List.map_ofFn]
    rfl

structure CurvatureParams where
  n : ℕ
  H : Matrix (Fin n) (Fin n) ℚ
  a : ℚ
  M : ℚ
  s : ℚ
  rho : ℚ
abbrev curvatureDataCode := prodCode natCode (prodCode matrixCode (prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode))))
def CurvatureParams.data (p : CurvatureParams) := (p.n,(matrixData p.H,(p.a,(p.M,(p.s,p.rho)))))
def curvatureCode (p : CurvatureParams) : Word := curvatureDataCode p.data
def curvatureView : Realizes curvatureCode curvatureDataCode CurvatureParams.data :=
  (identity curvatureDataCode).reindex curvatureCode CurvatureParams.data (fun _ => rfl)
def cuN := curvatureView.then (first natCode (prodCode matrixCode (prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode)))))
def cuRest := curvatureView.then (second natCode (prodCode matrixCode (prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode)))))
def cuH := cuRest.then (first matrixCode (prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode))))
def cuScalars := cuRest.then (second matrixCode (prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode))))
def cuA := cuScalars.then (first ratCode (prodCode ratCode (prodCode ratCode ratCode)))
def cuMore := cuScalars.then (second ratCode (prodCode ratCode (prodCode ratCode ratCode)))
def cuM := cuMore.then (first ratCode (prodCode ratCode ratCode))
def cuLast := cuMore.then (second ratCode (prodCode ratCode ratCode))
def cuS := cuLast.then (first ratCode ratCode)
def cuRho := cuLast.then (second ratCode ratCode)

def cuShift : Realizes curvatureCode matrixObjectCode
    (fun p => ⟨p.n,RationalRoot.shiftedHessian p.H p.a⟩) :=
  let c (q : ℚ) := constant curvatureCode ratCode q
  let shift := ((cuH.both ((((c 7).mul cuA).both (cuN.then identityMatrix)).then matrixScale)).then matrixAdd)
  (cuN.both shift).changeOutput matrixObjectCode
    (fun p => ⟨p.n,RationalRoot.shiftedHessian p.H p.a⟩) (by
      intro p
      simp only [identityMatrix_data,matrixScale_data]
      change prodCode natCode matrixCode (p.n,
        zipDefault (zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0) [] []
          (matrixData p.H,matrixData ((7*p.a) • (1 : Matrix (Fin p.n) (Fin p.n) ℚ))))=_
      rw [matrixAdd_data]
      rfl)

def computedCurvature : Realizes curvatureCode vectorCode
    (fun p => (RationalRoot.computedCurvature p.H p.a p.M p.s p.rho).elim [] List.ofFn) :=
  let c (q : ℚ) := constant curvatureCode ratCode q
  let v := cuShift.then psdStored
  let beta := cuA.div ((c 4096).mul cuM)
  let w := ((beta.both v).then normalizeVector)
  let factor := cuS.mul ((c 1).sub (cuA.div ((c 1024).mul cuM)))
  let scaled := (factor.both w).then vectorScale
  ((cuRho.both scaled).then roundMesh).congr (by
    intro p
    unfold RationalRoot.computedCurvature RationalRoot.negativeDirection
    cases hh : KS.W17.rationalNegativeWitness p.n (RationalRoot.shiftedHessian p.H p.a) with
    | none => simp [witnessData,hh,normalizeData,initialScaleData]
    | some v =>
      simp only [witnessData,hh,Option.elim_some,Option.map_some,normalize_data,vectorScale_ofFn,roundMesh_data]
      rfl)

end CurrentKS.Realization

end

end OAI
